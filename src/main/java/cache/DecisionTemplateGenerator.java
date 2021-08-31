package cache;

import cache.labels.EqualityLabel;
import cache.labels.Label;
import cache.labels.ReturnedRowLabel;
import cache.trace.QueryTrace;
import cache.trace.QueryTraceEntry;
import cache.trace.QueryTupleIdxPair;
import cache.trace.SubQueryTrace;
import cache.unsat_core.AbstractUnsatCoreEnumerator;
import cache.unsat_core.Order;
import cache.unsat_core.ReturnedRowUnsatCoreEnumerator;
import cache.unsat_core.UnsatCoreEnumerator;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import policy_checker.Policy;
import solver.MyZ3Context;
import solver.Query;
import solver.Schema;
import util.UnionFind;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static util.TerminalColor.*;

public class DecisionTemplateGenerator {
    private final Schema schema;
    private final QueryTrace trace;
    private final Collection<Policy> policies;
    private final Collection<Query> views;

    public DecisionTemplateGenerator(Schema schema, Collection<Policy> policies, Collection<Query> views,
                                     QueryTrace trace) {
        this.schema = schema;
        this.policies = policies;
        this.views = views;
        this.trace = trace;
    }

    private Collection<Collection<ReturnedRowLabel>> findRRCores() {
        MyZ3Context context = schema.getContext();
//        Solver solver = context.mkSolver(context.mkSymbol("QF_UF"));
        Solver solver = context.mkSolver();

        BoundedUnsatCoreDeterminacyFormula formula = BoundedUnsatCoreDeterminacyFormula.create(schema, policies, views, trace,
                BoundedUnsatCoreDeterminacyFormula.LabelOption.RETURNED_ROWS_ONLY);
        solver.add(Iterables.toArray(formula.makeBackgroundFormulas(), BoolExpr.class));

        Collection<Collection<ReturnedRowLabel>> rrCores;
        // In `RETURNED_ROWS_ONLY` mode, all `labeledExprs` should be of type `ReturnedRowLabel`.
        Map<ReturnedRowLabel, BoolExpr> labeledExprs = formula.makeLabeledExprs()
                .entrySet().stream().collect(Collectors.toMap(
                        e -> (ReturnedRowLabel) e.getKey(),
                        Map.Entry::getValue)
                );
        try (UnsatCoreEnumerator<ReturnedRowLabel> uce =
                     new UnsatCoreEnumerator<>(context, solver, labeledExprs, Order.ARBITRARY)) {
            rrCores = uce.enumerateAll();
        }
        System.out.println(ANSI_BLUE_BACKGROUND + ANSI_RED + rrCores + ANSI_RESET);
        return rrCores;
    }

    public Collection<DecisionTemplate> generate() {
        // Step 1: Find all minimal unsat cores among the returned-row labels, assuming all equalities hold.
//        Collection<Collection<ReturnedRowLabel>> rrCores = findRRCores();
        Collection<Collection<ReturnedRowLabel>> rrCores = ReturnedRowUnsatCoreEnumerator.create(
                schema, views, trace
        ).enumerateAll();
        System.out.println(ANSI_BLUE_BACKGROUND + ANSI_RED + rrCores + ANSI_RESET);

        // Step 2: For each unsat core among query labels, enumerate unsat cores among equality labels.
        MyZ3Context context = schema.getContext();
        ArrayList<DecisionTemplate> dts = new ArrayList<>();
        for (Collection<ReturnedRowLabel> rrCore : rrCores) {
            ImmutableList<QueryTupleIdxPair> toKeep = rrCore.stream()
                    .map(rrl -> new QueryTupleIdxPair(rrl.getQueryIdx(), rrl.getRowIdx()))
                    .collect(ImmutableList.toImmutableList());
            SubQueryTrace sqt = trace.getSubTrace(toKeep);
            BoundedUnsatCoreDeterminacyFormula formula = BoundedUnsatCoreDeterminacyFormula.create(schema, policies, views, sqt,
                    BoundedUnsatCoreDeterminacyFormula.LabelOption.ALL);

            Map<Label, BoolExpr> labeledExprs = formula.makeLabeledExprs();
            ImmutableSet<EqualityLabel.Operand> allNonValueOperandsOld =
                    labeledExprs.keySet().stream() // Get all labels.
                            .filter(l -> l.getKind() == Label.Kind.EQUALITY) // Keep only equality labels.
                            .map(l -> (EqualityLabel) l)
                            .flatMap(el -> Stream.of(el.getLhs(), el.getRhs())) // Gather both operands of each label.
                            .filter(o -> o.getKind() != EqualityLabel.Operand.Kind.VALUE) // Keep only non-value operands.
                            .map(o -> backMapOperand(o, sqt))
                            .collect(ImmutableSet.toImmutableSet());

            Solver solver = context.mkSolver(context.mkSymbol("QF_UF"));
            solver.add(Iterables.toArray(formula.makeBackgroundFormulas(), BoolExpr.class));
            try (UnsatCoreEnumerator<Label> uce =
                         new UnsatCoreEnumerator<>(context, solver, labeledExprs, Order.INCREASING)) {
                Optional<Set<Label>> ret;
                for (int i = 0; i < 1 && (ret = uce.next()).isPresent(); ++i) {
                    List<Label> coreLabelsOld = ret.get().stream().map(l -> backMapLabel(l, sqt))
                            .collect(Collectors.toList());
                    dts.add(buildDecisionTemplate(coreLabelsOld, allNonValueOperandsOld));
                }
            }
        }

        checkState(!dts.isEmpty(), "should have generated at least one decision template");
        return dts;
    }

    private EqualityLabel.Operand backMapOperand(EqualityLabel.Operand o, SubQueryTrace sqt) {
        switch (o.getKind()) {
            case CONTEXT_CONSTANT:
            case VALUE:
                return o;
            case QUERY_PARAM:
                EqualityLabel.QueryParamOperand qpo = (EqualityLabel.QueryParamOperand) o;
                if (qpo.isCurrentQuery()) {
                    return qpo;
                }
                int oldQueryIdx = sqt.getQueryIdxBackMap().get(qpo.getQueryIdx());
                return new EqualityLabel.QueryParamOperand(oldQueryIdx, false, qpo.getParamIdx());
            case RETURNED_ROW_ATTR:
                EqualityLabel.ReturnedRowFieldOperand rrfo = (EqualityLabel.ReturnedRowFieldOperand) o;
                QueryTupleIdxPair old = sqt.getBackMap().get(
                        new QueryTupleIdxPair(rrfo.getQueryIdx(), rrfo.getReturnedRowIdx()));
                return new EqualityLabel.ReturnedRowFieldOperand(old.getQueryIdx(), old.getTupleIdx(), rrfo.getColIdx());
        }
        checkArgument(false, "invalid operand kind: " + o.getKind());
        return null;
    }

    private Label backMapLabel(Label l, SubQueryTrace sqt) {
        switch (l.getKind()) {
            case EQUALITY:
                EqualityLabel el = (EqualityLabel) l;
                return new EqualityLabel(backMapOperand(el.getLhs(), sqt), backMapOperand(el.getRhs(), sqt));
            case RETURNED_ROW:
                ReturnedRowLabel rrl = (ReturnedRowLabel) l;
                QueryTupleIdxPair old = sqt.getBackMap().get(new QueryTupleIdxPair(rrl.getQueryIdx(), rrl.getRowIdx()));
                return new ReturnedRowLabel(old.getQueryIdx(), old.getTupleIdx());
        }
        checkArgument(false, "invalid label kind: " + l.getKind());
        return null;
    }

    private DecisionTemplate buildDecisionTemplate(List<Label> unsatCore,
                                                   Set<EqualityLabel.Operand> allNonValueOperands) {
        // Find all equivalence classes consisting of non-value operands.
        // If an equivalence class is equal to a value, the value is attached as data in the union-find.
        UnionFind<EqualityLabel.Operand> uf = new UnionFind<>(allNonValueOperands);
        for (Label l : unsatCore) {
            if (l.getKind() != Label.Kind.EQUALITY) {
                continue;
            }

            EqualityLabel el = (EqualityLabel) l;
            EqualityLabel.Operand lhs = el.getLhs(), rhs = el.getRhs();
            if (lhs.getKind() == EqualityLabel.Operand.Kind.VALUE) {
                EqualityLabel.Operand temp = lhs;
                lhs = rhs;
                rhs = temp;
            }
            checkState(lhs.getKind() != EqualityLabel.Operand.Kind.VALUE,
                    "equality of the form value=value should not appear");

            if (rhs.getKind() == EqualityLabel.Operand.Kind.VALUE) {
                uf.attachData(lhs, ((EqualityLabel.ValueOperand) rhs).getValue());
            } else {
                uf.union(lhs, rhs);
            }
        }

        // Assign consecutive indexes (starting from 0) to roots, excluding those with only one element and those
        // with a concrete value attached.
        Map<EqualityLabel.Operand, Integer> root2Index = new HashMap<>();
        for (EqualityLabel.Operand root : uf.getRoots()) {
            UnionFind<EqualityLabel.Operand>.EquivalenceClass ec = uf.findComplete(root);
            if (ec.getDatum() == null && ec.getSize() >= 2) {
                root2Index.put(root, root2Index.size());
            }
        }

        List<QueryTraceEntry> allTraceEntries = trace.getAllEntries();
        Map<Integer, Map<Integer, DecisionTemplate.EntryBuilder>> queryIdx2rowEBs = new HashMap<>();
        for (Label l : unsatCore) {
            if (l.getKind() != Label.Kind.RETURNED_ROW) {
                continue;
            }
            ReturnedRowLabel rrl = (ReturnedRowLabel) l;
            int queryIdx = rrl.getQueryIdx();

            Map<Integer, DecisionTemplate.EntryBuilder> rowEBs =
                    queryIdx2rowEBs.computeIfAbsent(queryIdx, k -> new HashMap<>());

            int rowIdx = rrl.getRowIdx();
            checkState(!rowEBs.containsKey(rowIdx));
            DecisionTemplate.EntryBuilder eb = new DecisionTemplate.EntryBuilder(allTraceEntries.get(queryIdx), false);
            rowEBs.put(rowIdx, eb);
        }
        DecisionTemplate.EntryBuilder currEB = new DecisionTemplate.EntryBuilder(trace.getCurrentQuery(), true);

        ImmutableMap.Builder<String, Integer> constName2ECBuilder = new ImmutableMap.Builder<>();
        ImmutableMap.Builder<String, Object> constName2ValueBuilder = new ImmutableMap.Builder<>();

        for (EqualityLabel.Operand o : allNonValueOperands) {
            UnionFind<EqualityLabel.Operand>.EquivalenceClass ec = uf.findComplete(o);
            Object datum = ec.getDatum();
            if (datum == null && ec.getSize() < 2) {
                continue;
            }

            switch (o.getKind()) {
                case CONTEXT_CONSTANT:
                    String constName = ((EqualityLabel.ContextConstantOperand) o).getName();
                    if (datum == null) {
                        constName2ECBuilder.put(constName, root2Index.get(ec.getRoot()));
                    } else {
                        constName2ValueBuilder.put(constName, datum);
                    }
                    break;
                case QUERY_PARAM:
                    EqualityLabel.QueryParamOperand qpo = (EqualityLabel.QueryParamOperand) o;
                    // Set param for all entry builder(s) for this query.
                    Collection<DecisionTemplate.EntryBuilder> ebs =
                            qpo.isCurrentQuery() ? List.of(currEB) :
                                    queryIdx2rowEBs.getOrDefault(qpo.getQueryIdx(), Collections.emptyMap())
                                            .values();
                    // If the query index is not in `queryIdx2rowEBs`, the query is irrelevant and so we ignore.
                    ebs.forEach(
                            datum == null ?
                                    eb -> eb.setParamEC(qpo.getParamIdx(), root2Index.get(ec.getRoot())) :
                                    eb -> eb.setParamValue(qpo.getParamIdx(), datum)
                    );
                    break;
                case RETURNED_ROW_ATTR:
                    EqualityLabel.ReturnedRowFieldOperand rrfo = (EqualityLabel.ReturnedRowFieldOperand) o;
                    Map<Integer, DecisionTemplate.EntryBuilder> rowEBs = queryIdx2rowEBs.get(rrfo.getQueryIdx());
                    if (rowEBs == null) { // This query is irrelevant.
                        break;
                    }
                    DecisionTemplate.EntryBuilder eb = rowEBs.get(rrfo.getReturnedRowIdx());
                    if (eb == null) { // This returned row is irrelevant.
                        break;
                    }
                    if (datum == null) {
                        eb.setRowAttrEC(rrfo.getColIdx(), root2Index.get(ec.getRoot()));
                    } else {
                        eb.setRowAttrValue(rrfo.getColIdx(), datum);
                    }
                    break;
                default:
                    assert false;
            }
        }

        ImmutableList.Builder<DecisionTemplate.Entry> entriesBuilder = new ImmutableList.Builder<>();
        entriesBuilder.add(currEB.build());
        for (Map<Integer, DecisionTemplate.EntryBuilder> rowEBs : queryIdx2rowEBs.values()) {
            for (DecisionTemplate.EntryBuilder eb : rowEBs.values()) {
                entriesBuilder.add(eb.build());
            }
        }
        return new DecisionTemplate(entriesBuilder.build(), constName2ECBuilder.build(), constName2ValueBuilder.build());
    }
}
