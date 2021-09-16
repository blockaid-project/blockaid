package solver;

import cache.trace.QueryTraceEntry;
import cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Streams;
import com.microsoft.z3.*;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import solver.context.MyZ3Context;
import util.UnionFind;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.google.common.base.Preconditions.checkState;

public abstract class DeterminacyFormula {
    private static final boolean MERGE_TRACE = false;

    protected final MyZ3Context context;
    protected final Schema schema;
    protected final Instance inst1;
    protected final Instance inst2;

    protected final ImmutableList<BoolExpr> preamble;
    private final String preambleSMT;

    public enum TextOption {
        USE_TEXT,
        NO_TEXT
    }

    protected final TextOption textOption;

    protected DeterminacyFormula(Schema schema, Function<Integer, Instance> makeInstance,
                                 BiFunction<Instance, Instance, List<BoolExpr>> mkPreamble,
                                 TextOption text) {
        this.schema = schema;
        this.context = schema.getContext();
        this.inst1 = makeInstance.apply(0);
        this.inst2 = makeInstance.apply(1);

        // Set prepared expr.
        final long startTime = System.currentTimeMillis();

        this.preamble = ImmutableList.copyOf(mkPreamble.apply(this.inst1, this.inst2));
        this.textOption = text;
        if (text == TextOption.USE_TEXT) {
            Solver solver = schema.getContext().mkRawSolver();
            solver.add(this.preamble.toArray(new BoolExpr[0]));
            String result = solver.toString();
            // Remove the custom sorts from preamble -- we add them back when generating the rest of the formula,
            // because here, sorts that are not used in the preamble but are used later on won't be declared.
            result = result.replaceAll("\\(declare-sort CS![A-Z]+ 0\\)|\\(declare-fun CS![A-Z]+!\\d+ \\(\\) CS![A-Z]+\\)", "");
            // FIXME(zhangwen): this is janky.
            result = result.replaceAll("\\(declare-fun [A-Za-z]+ \\(CS!INT CS!INT\\) Bool\\)", "");

            if (!result.contains("!_NOW")) {
                result += "(declare-fun !_NOW () CS!INT)\n";
            }
            context.mkConst("!_NOW", context.getCustomIntSort());
            this.preambleSMT = result;
        } else {
            this.preambleSMT = null;
        }
//        System.out.println("set prepared expr " + getClass().getName() + ":" + (System.currentTimeMillis() - startTime));
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
        /* Both regular and fast unsat share this formula form -- by symmetry, we can write Q(D1) != Q(D2) using
        "not contained in". */
        Query query = queries.getCurrentQuery().getQuery().getSolverQuery(schema);
        Tuple extHeadTup = query.makeFreshHead();
        List<BoolExpr> res = Lists.newArrayList(query.apply(inst1).doesContainExpr(extHeadTup));
        res.add(context.mkNot(
                context.mkAnd(query.apply(inst2).doesContainExpr(extHeadTup))
        ));
        return res;
    }

    public Iterable<BoolExpr> makeBodyFormula(UnmodifiableLinearQueryTrace queries) {
        return Iterables.concat(generateTupleCheck(queries), generateConstantCheck(queries),
                generateNotContains(queries));
    }

    public String generateSMT(UnmodifiableLinearQueryTrace queries) {
        return generateSMT(() -> makeBodyFormula(queries));
    }

    protected String generateSMT(Supplier<Iterable<BoolExpr>> mkBody) {
        checkState(textOption == TextOption.USE_TEXT);

        context.startTrackingConsts();
        String bodyFormula = Streams.stream(mkBody.get())
                .map(formula -> "(assert " + formula + ")")
                .collect(Collectors.joining("\n"));
        context.stopTrackingConsts();

        StringBuilder sb = new StringBuilder();
        for (Expr constant : context.getConsts()) {
            if (!constant.getSExpr().startsWith("CS!")) {
                sb.append("(declare-fun ").append(constant.getSExpr()).append(" () ").append(constant.getSort().getSExpr()).append(")\n");
            }
        }
        sb.append(bodyFormula);
        String body = sb.toString();

        // only used to generate declarations and assertions for sorts
        String header = context.prepareSortDeclaration();
        return header + this.preambleSMT + body + "(check-sat)";
    }
}
