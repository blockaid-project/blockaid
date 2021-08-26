package cache;

import cache.labels.EqualityLabel;
import cache.labels.Label;
import cache.labels.ReturnedRowLabel;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
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

import static com.google.common.base.Preconditions.checkState;
import static util.TerminalColor.*;

public class DecisionTemplateGenerator {
    private final Schema schema;
    private final QueryTrace trace;
    private final MyUnsatCoreDeterminacyFormula formula;

    public DecisionTemplateGenerator(Schema schema, Collection<Policy> policies, Collection<Query> views,
                                     QueryTrace trace) {
        this.schema = schema;
        this.trace = trace;

        long startTime = System.currentTimeMillis();
        this.formula = MyUnsatCoreDeterminacyFormula.create(schema, policies, views, trace);
        System.out.println("\t\t| Formula constructor:\t" + (System.currentTimeMillis() - startTime));
    }

    public Collection<DecisionTemplate> generate() {
        MyZ3Context context = schema.getContext();
        Solver solver = context.mkRawSolver();
        solver.add(formula.makeMainFormula().toArray(BoolExpr[]::new));

        Map<Label, BoolExpr> labeledExprs = formula.makeLabeledExprs();
        Map<BoolExpr, Label> boolConst2Label = new HashMap<>();
        Set<EqualityLabel.Operand> allNonValueOperands = new HashSet<>();
        for (Map.Entry<Label, BoolExpr> entry : labeledExprs.entrySet()) {
            Label l = entry.getKey();
            BoolExpr boolConst = context.mkBoolConst(l.toString());
            checkState(!boolConst2Label.containsKey(boolConst));
            boolConst2Label.put(boolConst, l);

            if (l.getKind() == Label.Kind.EQUALITY) {
                EqualityLabel el = (EqualityLabel) l;
                EqualityLabel.Operand lhs = el.getLhs(), rhs = el.getRhs();
                if (lhs.getKind() != EqualityLabel.Operand.Kind.VALUE) {
                    allNonValueOperands.add(el.getLhs());
                }
                if (rhs.getKind() != EqualityLabel.Operand.Kind.VALUE) {
                    allNonValueOperands.add(el.getRhs());
                }
            }
        }

        // Step 1: Find all minimal unsat cores among the returned-row labels, assuming all equalities hold.
        Collection<Collection<ReturnedRowLabel>> rrCores;
        {
            solver.push();
            solver.add(formula.getAllEquality().toArray(new BoolExpr[0]));
            HashMap<ReturnedRowLabel, BoolExpr> rrLabeledExprs = new HashMap<>();
            for (Map.Entry<Label, BoolExpr> entry : labeledExprs.entrySet()) {
                Label l = entry.getKey();
                if (l.getKind() == Label.Kind.RETURNED_ROW) {
                    rrLabeledExprs.put((ReturnedRowLabel) l, entry.getValue());
                }
            }
            try (UnsatCoreEnumerator<ReturnedRowLabel> uce =
                         new UnsatCoreEnumerator<>(context, solver, rrLabeledExprs)) {
                rrCores = uce.enumerateAll();
            }
            System.out.println(ANSI_BLUE_BACKGROUND + ANSI_RED + rrCores + ANSI_RESET);
            solver.pop();
        }

        // Step 2: For each unsat core among query labels, enumerate unsat cores among equality labels.
        ArrayList<DecisionTemplate> dts = new ArrayList<>();
        for (Collection<ReturnedRowLabel> rrCore : rrCores) {
            Set<Integer> qIndices = rrCore.stream().map(ReturnedRowLabel::getQueryIdx).collect(Collectors.toSet());

            // Disregard equality labels that refer to parameters from irrelevant queries / attributes of irrelevant
            // returned rows.
            HashMap<EqualityLabel, BoolExpr> keptLabeledExprs = new HashMap<>();
            for (Map.Entry<Label, BoolExpr> entry : labeledExprs.entrySet()) {
                Label l = entry.getKey();
                if (l.getKind() != Label.Kind.EQUALITY) {
                    continue;
                }
                EqualityLabel el = (EqualityLabel) l;
                boolean shouldDiscard = Stream.of(el.getLhs(), el.getRhs()).anyMatch(o -> {
                    // Returns true if this operand causes the label to be DISCARDED.
                    switch (o.getKind()) {
                        case QUERY_PARAM:
                            EqualityLabel.QueryParamOperand qpo = (EqualityLabel.QueryParamOperand) o;
                            if (qpo.isCurrentQuery()) {
                                return false;
                            }
                            return !qIndices.contains(qpo.getQueryIdx());
                        case RETURNED_ROW_ATTR:
                            EqualityLabel.ReturnedRowFieldOperand rro = (EqualityLabel.ReturnedRowFieldOperand) o;
                            return !rrCore.contains(new ReturnedRowLabel(rro.getQueryIdx(), rro.getReturnedRowIdx()));
                    }
                    return false; // Other operands (value, context constant) don't contribute to the decision.
                });
                if (!shouldDiscard) {
                    keptLabeledExprs.put(el, entry.getValue());
                }
            }
            System.out.println(ANSI_BLUE_BACKGROUND + ANSI_RED + keptLabeledExprs.keySet() + ANSI_RESET);

            solver.push();
            solver.add(rrCore.stream().map(labeledExprs::get).toArray(BoolExpr[]::new));
            try (UnsatCoreEnumerator<EqualityLabel> uce =
                         new UnsatCoreEnumerator<>(context, solver, keptLabeledExprs)) {
                Optional<Set<EqualityLabel>> ret;
                for (int i = 0; i < 1 && (ret = uce.next()).isPresent(); ++i) {
                    ArrayList<Label> coreLabels = new ArrayList<>(ret.get());
                    coreLabels.addAll(rrCore);
                    dts.add(buildDecisionTemplate(coreLabels, allNonValueOperands));
                }
            }
            solver.pop();
        }

        return dts;
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
