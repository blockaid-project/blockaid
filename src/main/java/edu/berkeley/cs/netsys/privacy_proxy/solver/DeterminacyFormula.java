package edu.berkeley.cs.netsys.privacy_proxy.solver;

import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Streams;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import org.checkerframework.checker.nullness.qual.Nullable;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.TrackedDecls;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public class DeterminacyFormula<C extends Z3ContextWrapper<?, ?, ?, ?>, I extends Instance<C>> {
    protected final C context;
    protected final Schema<C> schema;
    protected final I inst1;
    protected final I inst2;

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

    protected DeterminacyFormula(Schema<C> schema, I inst1, I inst2, Collection<BoolExpr> preamble,
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

    protected DeterminacyFormula(Schema<C> schema, Function<Integer, I> mkInst,
                                 BiFunction<I, I, List<BoolExpr>> mkPreamble, TextOption text) {
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

    protected DeterminacyFormula(Schema<C> schema, Function<Integer, I> makeInstance,
            BiFunction<I, I, List<BoolExpr>> mkPreamble)
    {
        this(schema, makeInstance, mkPreamble, TextOption.USE_TEXT);
    }

    public static <C extends Z3ContextWrapper<?, ?, ?, ?>> List<Tuple<C>> getTupleObjects(QueryTraceEntry qte, Schema<C> schema) {
        return qte.getTuplesStream().map(
                tuple -> new Tuple<>(schema, tuple.stream().map(
                        v -> schema.getContext().getExprForValue(v)
                ))).collect(Collectors.toList());
    }

    protected Iterable<BoolExpr> generateTupleCheck(UnmodifiableLinearQueryTrace queries) {
        List<BoolExpr> exprs = new ArrayList<>();
        for (QueryTraceEntry queryTraceEntry : queries.getAllEntries()) {
            Query<C> query = queryTraceEntry.getQuery().getSolverQuery(schema);
            Relation<C> r1 = query.apply(inst1);
            List<Tuple<C>> tuples = getTupleObjects(queryTraceEntry, schema);
            for (Tuple<C> tup : tuples) {
                Iterables.addAll(exprs, r1.doesContainExpr(tup));
            }
        }

        return exprs;
    }

    protected Iterable<BoolExpr> generateConstantCheck(UnmodifiableLinearQueryTrace queries) {
        List<BoolExpr> exprs = new ArrayList<>();
        // Constrain constant values.
        for (Map.Entry<String, Object> entry : queries.getConstMap().entrySet()) {
            Object value = entry.getValue();
            exprs.add(context.mkEq(
                    context.mkConst("!" + entry.getKey(), context.getSortForValue(value)),
                    context.getExprForValue(entry.getValue())
            ));
        }

        return exprs;
    }

    protected Iterable<BoolExpr> generateNotContains(UnmodifiableLinearQueryTrace queries) {
        return generateNotContains(queries.getCurrentQuery().getQuery().getSolverQuery(schema));
    }

    protected Iterable<BoolExpr> generateNotContains(Query<C> query) {
        /* Both regular and fast unsat share this formula form -- by symmetry, we can write Q(D1) != Q(D2) using
        "not contained in". */
        Tuple<C> extHeadTup = query.makeFreshExistentialHead();
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
            for (FuncDecl<?> funcDecl : decls.getFuncDecls()) {
                sb.append(funcDecl.getSExpr()).append("\n");
            }
            for (Expr<?> constant : decls.getConsts()) {
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
}
