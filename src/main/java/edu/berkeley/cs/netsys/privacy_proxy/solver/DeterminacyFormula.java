package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.*;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.DependencyLabel;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.PreambleLabel;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.PolicyLabel;
import org.checkerframework.checker.nullness.qual.Nullable;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.TrackedDecls;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkState;

/**
 * Base determinacy formula class.  A preamble should be supplied at instantiation.
 * @param <C> The type of the context.
 * @param <I> The type of the instance.
 */
public class DeterminacyFormula<C extends Z3ContextWrapper<?, ?, ?, ?>, I extends Instance<C>> {
    protected final C context;
    protected final Schema<C> schema;
    protected final I inst1;
    protected final I inst2;

    /**
     * Maps a label to the components of a conjunction that constitutes the formula for the label.
     */
    protected final ImmutableMap<PreambleLabel, ImmutableList<BoolExpr>> preamble;

    private final @Nullable ImmutableMap<PreambleLabel, String> preambleSMT;

    protected final TextOption textOption;

    protected static ImmutableMap<PreambleLabel, String> makePreambleSMTNamed(Map<PreambleLabel, NamedBoolExpr> exprs) {
        return ImmutableMap.copyOf(Maps.transformValues(exprs, NamedBoolExpr::makeAssertion));
    }

    protected static ImmutableMap<PreambleLabel, String> makePreambleSMT(Map<PreambleLabel, ImmutableList<BoolExpr>> exprs) {
        ImmutableMap.Builder<PreambleLabel, String> builder = ImmutableMap.builder();
        for (Map.Entry<PreambleLabel, ImmutableList<BoolExpr>> entry : exprs.entrySet()) {
            ImmutableList<BoolExpr> expressions = entry.getValue();
            String assertions = expressions.stream()
                    .map(e -> "(assert " + e.getSExpr() + ")")
                    .collect(Collectors.joining("\n"));
            builder.put(entry.getKey(), assertions);
        }
        return builder.build();
    }

    public DeterminacyFormula(Schema<C> schema, I inst1, I inst2,
                              Map<PreambleLabel, ImmutableList<BoolExpr>> preamble,
                              TextOption text, Map<PreambleLabel, String> preambleSMT) {
        this.schema = schema;
        this.context = schema.getContext();
        this.inst1 = inst1;
        this.inst2 = inst2;
        this.preamble = ImmutableMap.copyOf(preamble);
        this.textOption = text;
        this.preambleSMT = switch (text) {
            case USE_TEXT -> ImmutableMap.copyOf(preambleSMT);
            case NO_TEXT -> null;
        };
    }

    public DeterminacyFormula(Schema<C> schema, Function<Integer, I> mkInst,
                              BiFunction<I, I, Map<PreambleLabel, ImmutableList<BoolExpr>>> mkPreamble,
                              TextOption text) {
        this.schema = schema;
        this.context = schema.getContext();
        this.inst1 = mkInst.apply(0);
        this.inst2 = mkInst.apply(1);

        this.preamble = ImmutableMap.copyOf(mkPreamble.apply(this.inst1, this.inst2));
        this.textOption = text;
        this.preambleSMT = switch (text) {
            case USE_TEXT -> makePreambleSMT(this.preamble);
            case NO_TEXT -> null;
        };
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
            exprs.add(context.mkIsSameValue(
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
        return Iterables.concat(
                generateTupleCheck(queries),
                generateConstantCheck(queries),
                generateNotContains(queries));
    }

    public String generateSMT(UnmodifiableLinearQueryTrace queries) {
        return generateSMT(makeBodyFormula(queries), computeRelevantPreambleLabels(queries));
    }

    private void appendPreamble(StringBuilder sb, Set<PreambleLabel> chosen) {
        checkState(preambleSMT != null, "cannot append preamble in NO_TEXT mode");
        for (Map.Entry<PreambleLabel, String> entry : preambleSMT.entrySet()) {
            if (chosen.contains(entry.getKey())) {
                sb.append(entry.getValue()).append("\n");
            }
        }
    }

    protected String generateSMTFromString(String bodySMT, String extraHeader, String extraFooter,
                                           Set<PreambleLabel> chosenPreambleLabels) {
        checkState(textOption == TextOption.USE_TEXT, "cannot generate SMT in NO_TEXT mode");

        context.pushTrackConsts();
        try {
            StringBuilder sb = new StringBuilder();

            sb.append(extraHeader);

            // Make header.
            sb.append(context.prepareSortDeclaration());
            TrackedDecls decls = context.getAllTrackedDecls();
            for (FuncDecl<?> funcDecl : decls.getFuncDecls()) {
                sb.append(funcDecl.getSExpr()).append("\n");
            }
            for (Expr<?> constant : decls.getConsts()) {
                sb.append("(declare-fun ").append(constant.getSExpr()).append(" () ").append(constant.getSort().getSExpr()).append(")\n");
            }

            appendPreamble(sb, chosenPreambleLabels);
            sb.append(bodySMT)
                    .append(context.prepareCustomValueConstraints())
                    .append("(check-sat)\n")
                    .append(extraFooter);
            return sb.toString();
        } finally {
            context.popTrackConsts();
        }
    }
    protected String generateSMT(Stream<BoolExpr> body, Set<PreambleLabel> chosenPreambleLabels) {
        String bodySMT = body.map(formula -> "(assert " + formula + ")")
                .collect(Collectors.joining("\n"));
        return generateSMTFromString(bodySMT, "", "", chosenPreambleLabels);
    }

    protected String generateSMT(Iterable<BoolExpr> body, Set<PreambleLabel> chosenPreambleLabels) {
        return generateSMT(Streams.stream(body), chosenPreambleLabels);
    }

    public Set<PreambleLabel> computeRelevantPreambleLabels(UnmodifiableLinearQueryTrace trace) {
        HashSet<PreambleLabel> labels = new HashSet<>();
        Set<String> relevantTables = schema.computeRelevantTables(trace);

        for (PreambleLabel l : preamble.keySet()) {
            if (l instanceof PolicyLabel vl) {
                Set<String> relationsInPolicy = vl.policy().getParsedPSJ().getRelations();
                if (relevantTables.containsAll(relationsInPolicy)) {
                    labels.add(vl);
                }
            } else if (l instanceof DependencyLabel dl) {
                if (relevantTables.containsAll(dl.dependency().getCriticalRelations())) {
                    labels.add(dl);
                }
            } else {
                throw new IllegalArgumentException("Unknown label type: " + l);
            }
        }

        return labels;
    }
}
