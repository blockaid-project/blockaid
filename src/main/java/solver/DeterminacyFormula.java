package solver;

import cache.trace.QueryTraceEntry;
import cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Streams;
import com.microsoft.z3.*;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import org.checkerframework.checker.nullness.qual.Nullable;
import solver.context.MyZ3Context;
import solver.context.TrackedDecls;
import util.UnionFind;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public class DeterminacyFormula {
    private static final boolean MERGE_TRACE = false;

    protected final MyZ3Context context;
    protected final Schema schema;
    protected final Instance inst1;
    protected final Instance inst2;

    protected final ImmutableList<BoolExpr> preamble;
    private final @Nullable String preambleSMT;

    protected final TextOption textOption;

    protected static String makePreambleSMTNamed(List<NamedBoolExpr> exprs) {
        return exprs.stream().map(NamedBoolExpr::makeAssertion).collect(Collectors.joining("\n"));
    }

    protected static String makePreambleSMT(List<BoolExpr> exprs) {
        StringBuilder sb = new StringBuilder();
        for (BoolExpr e : exprs) {
            sb.append("(assert ").append(e.getSExpr()).append(")\n");
        }
        return sb.toString();
    }

    protected DeterminacyFormula(Schema schema, Instance inst1, Instance inst2, Collection<BoolExpr> preamble,
                                 TextOption text, String preambleSMT) {
        this.schema = schema;
        this.context = schema.getContext();
        this.inst1 = inst1;
        this.inst2 = inst2;
        this.preamble = ImmutableList.copyOf(preamble);
        this.textOption = text;
        this.preambleSMT = switch (text) {
            case USE_TEXT -> checkNotNull(preambleSMT);
            case NO_TEXT -> null;
        };
    }

    protected DeterminacyFormula(Schema schema, Function<Integer, Instance> mkInst,
                                 BiFunction<Instance, Instance, List<BoolExpr>> mkPreamble,
                                 TextOption text) {
        this.schema = schema;
        this.context = schema.getContext();
        this.inst1 = mkInst.apply(0);
        this.inst2 = mkInst.apply(1);

        this.preamble = ImmutableList.copyOf(mkPreamble.apply(this.inst1, this.inst2));
        this.textOption = text;
        this.preambleSMT = switch (text) {
            case USE_TEXT -> makePreambleSMT(this.preamble);
            case NO_TEXT -> null;
        };
    }

    protected DeterminacyFormula(Schema schema, Function<Integer, Instance> makeInstance,
                                 BiFunction<Instance, Instance, List<BoolExpr>> mkPreamble) {
        this(schema, makeInstance, mkPreamble, TextOption.USE_TEXT);
    }

    // FIXME(zhangwen): this is ugly.
    private static boolean extractFact(Instance inst, BoolExpr e, Map<String, Map<Expr, UnionFind<Integer>>> facts) {
        if (inst.isConcrete) {
            return false;
        }
        if (!e.isQuantifier()) {
            return false;
        }
        Quantifier q = (Quantifier) e;
        if (!q.isExistential()) {
            return false;
        }
        Expr body = q.getBody();
        if (!body.isApp()) {
            return false;
        }
        FuncDecl fd = body.getFuncDecl();
        if (fd.getDeclKind() != Z3_decl_kind.Z3_OP_UNINTERPRETED) {
            return false;
        }
        String relationName = inst.getRelNameFromFuncDecl(fd);
        if (relationName == null) {
            return false;
        }
        Optional<ImmutableList<String>> oPkColumns = inst.schema.getRawSchema().getPrimaryKeyColumns(relationName);
        if (oPkColumns.isEmpty()) {
            return false;
        }
        List<String> pkColumns = oPkColumns.get();
        if (pkColumns.size() != 1) {
            return false;
        }
        List<String> columnNames = inst.schema.getColumnNames(relationName);
        int pkIdx = columnNames.indexOf(pkColumns.get(0));
        checkState(pkIdx >= 0);

        Expr[] args = body.getArgs();
        Expr pk = args[pkIdx];
        if (pk.isVar()) {
            return false;
        }

        Map<Expr, UnionFind<Integer>> relFacts = facts.computeIfAbsent(relationName, _k -> new HashMap<>());
        UnionFind<Integer> rowFacts = relFacts.computeIfAbsent(pk,
                _k -> new UnionFind<>(IntStream.range(0, columnNames.size()).boxed()));
        for (int i = 0; i < columnNames.size(); ++i) {
            if (!args[i].isVar()) {
                rowFacts.attachData(i, args[i]);
                continue;
            }
            for (int j = i + 1; j < columnNames.size(); ++j) {
                if (args[j].equals(args[i])) {
                    rowFacts.union(i, j);
                }
            }
        }
        return true;
    }

    private static List<BoolExpr> generateChecks(Instance inst, Map<String, Map<Expr, UnionFind<Integer>>> facts) {
        ArrayList<BoolExpr> checks = new ArrayList<>();

        Schema schema = inst.schema;
        MyZ3Context ctx = schema.getContext();
        for (Map.Entry<String, Map<Expr, UnionFind<Integer>>> relEntry : facts.entrySet()) {
            String relName = relEntry.getKey();
            List<Column> columns = schema.getColumns(relName);
            Relation rel = inst.get(relName);
            for (UnionFind<Integer> rowUF : relEntry.getValue().values()) {
                ArrayList<Expr> existentialVars = new ArrayList<>();
                Expr[] atomBody = new Expr[columns.size()];
                for (int i = 0; i < columns.size(); ++i) {
                    Expr e = (Expr) rowUF.findComplete(i).getDatum();
                    if (e == null) {
                        e = ctx.mkFreshConst("e", columns.get(i).type);
                        existentialVars.add(e);
                        // FIXME(zhangwen): when the value is null, the attached data conflict if the nulls are
                        //  represented as different constants.
                        rowUF.attachData(i, e);
                    }
                    atomBody[i] = e;
                }
                BoolExpr check = ctx.myMkExists(existentialVars,
                        ctx.mkAnd(rel.doesContainExpr(new Tuple(schema, atomBody))));
                checks.add(check);
            }
        }

        return checks;
    }

    public static List<Tuple> getTupleObjects(QueryTraceEntry qte, Schema schema) {
        return qte.getTuplesStream().map(
                tuple -> new Tuple(schema, tuple.stream().map(
                        v -> Tuple.getExprFromObject(schema.getContext(), v)
                ))).collect(Collectors.toList());
    }

    protected Iterable<BoolExpr> generateTupleCheck(UnmodifiableLinearQueryTrace queries) {
        // Table -> primary key -> union find of column indices.
        Map<String, Map<Expr, UnionFind<Integer>>> facts = new HashMap<>();

        List<BoolExpr> exprs = new ArrayList<>();
        for (QueryTraceEntry queryTraceEntry : queries.getAllEntries()) {
            Query query = queryTraceEntry.getQuery().getSolverQuery(schema);
            Relation r1 = query.apply(inst1);
            List<Tuple> tuples = getTupleObjects(queryTraceEntry, schema);
            for (Tuple tup : tuples) {
                for (BoolExpr e : r1.doesContainExpr(tup)) {
                    if (!MERGE_TRACE || extractFact(inst1, e, facts)) {
                        exprs.add(e);
                    }
//                    if (!extractFact(inst1, e, facts)) {
//                        exprs.add(e);
//                    }
                }
            }
        }

        if (MERGE_TRACE) {
            exprs.addAll(generateChecks(inst1, facts));
        }

        return exprs;
    }

    protected Iterable<BoolExpr> generateConstantCheck(UnmodifiableLinearQueryTrace queries) {
        List<BoolExpr> exprs = new ArrayList<>();
        // Constrain constant values.
        for (Map.Entry<String, Object> entry : queries.getConstMap().entrySet()) {
            Object value = entry.getValue();
            exprs.add(context.mkEq(
                    context.mkConst("!" + entry.getKey(), Tuple.getSortFromObject(context, value)),
                    context.mkCustom(entry.getValue())
            ));
        }

        return exprs;
    }

    protected Iterable<BoolExpr> generateNotContains(UnmodifiableLinearQueryTrace queries) {
        return generateNotContains(queries.getCurrentQuery().getQuery().getSolverQuery(schema));
    }

    protected Iterable<BoolExpr> generateNotContains(Query query) {
        /* Both regular and fast unsat share this formula form -- by symmetry, we can write Q(D1) != Q(D2) using
        "not contained in". */
        Tuple extHeadTup = query.makeFreshExistentialHead();
        List<BoolExpr> body = Lists.newArrayList(query.apply(inst1).doesContainExpr(extHeadTup));
        body.add(context.mkNot(
                context.mkAnd(query.apply(inst2).doesContainExpr(extHeadTup))
        ));
        // Quantifier elimination doesn't seem to do much for this one.
        return List.of(context.myMkExists(
                extHeadTup.toExprList(),
                context.mkAnd(body)
        ));
    }

    public Iterable<BoolExpr> makeBodyFormula(UnmodifiableLinearQueryTrace queries) {
        return Iterables.concat(generateTupleCheck(queries), generateConstantCheck(queries),
                generateNotContains(queries));
    }

    public String generateSMT(UnmodifiableLinearQueryTrace queries) {
        return generateSMT(() -> makeBodyFormula(queries));
    }

    protected String generateSMTFromString(Supplier<String> mkBodySMT, String extraHeader, String extraFooter) {
        checkState(textOption == TextOption.USE_TEXT);

        context.pushTrackConsts();
        try {
            String bodySMT = mkBodySMT.get();
            StringBuilder sb = new StringBuilder();
            sb.append(context.prepareSortDeclaration());
            TrackedDecls decls = context.getAllTrackedDecls();
            for (FuncDecl funcDecl : decls.getFuncDecls()) {
                sb.append(funcDecl.getSExpr()).append("\n");
            }
            for (Expr constant : decls.getConsts()) {
                sb.append("(declare-fun ").append(constant.getSExpr()).append(" () ").append(constant.getSort().getSExpr()).append(")\n");
            }
            String header = sb.toString();

            return extraHeader + header + this.preambleSMT + bodySMT + context.prepareCustomValueConstraints()
                    + "(check-sat)\n" + extraFooter;
        } finally {
            context.popTrackConsts();
        }
    }
    protected String generateSMTFromString(Supplier<String> mkBodySMT) {
        return generateSMTFromString(mkBodySMT, "", "");
    }

    protected String generateSMT(Supplier<Iterable<BoolExpr>> mkBody) {
        return generateSMTFromString(() ->
                Streams.stream(mkBody.get())
                        .map(formula -> "(assert " + formula + ")")
                        .collect(Collectors.joining("\n")));
    }

//    protected String generateUnsatCoreSMT(Supplier<Iterable<NamedBoolExpr>> mkBody) {
//        checkState(textOption == TextOption.USE_TEXT);
//
//        context.pushTrackConsts();
//        String bodyFormula = Streams.stream(mkBody.get())
//                .map(nb -> nb.name() == null ?
//                        "(assert " + nb.expr() + ")" :
//                        "(assert (! (" + nb.expr() + ") :named " + nb.name() + "))"
//                )
//                .collect(Collectors.joining("\n"));
//        TrackedDecls decls = context.popTrackConsts();
//
//        StringBuilder sb = new StringBuilder();
//        for (Expr constant : decls.getConsts()) {
//            if (!constant.getSExpr().startsWith("CS!")) {
//                sb.append("(declare-fun ").append(constant.getSExpr()).append(" () ").append(constant.getSort().getSExpr()).append(")\n");
//            }
//        }
//        sb.append(bodyFormula);
//        String body = sb.toString();
//
//        // only used to generate declarations and assertions for sorts
//        String header = context.prepareSortDeclaration();
//        return "(set-option :produce-unsat-cores true)\n" + header + this.preambleSMT + body + "(check-sat)\n(get-unsat-core)\n";
//    }
}
