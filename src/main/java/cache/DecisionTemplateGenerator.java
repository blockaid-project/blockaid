package cache;

import cache.labels.EqualityLabel;
import cache.labels.Label;
import cache.labels.ReturnedRowLabel;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import policy_checker.Policy;
import solver.MyZ3Context;
import solver.Query;
import solver.Schema;
import util.UnionFind;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;
import static util.TerminalColor.ANSI_RED;
import static util.TerminalColor.ANSI_RESET;

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
//            solver.assertAndTrack(entry.getValue(), boolConst);
            solver.add(context.mkImplies(boolConst, entry.getValue()));

            if (l instanceof EqualityLabel) {
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

//        long startTime = System.currentTimeMillis();
//        Status res = solver.check();
//        System.out.println("\t\t| Checking:\t" + (System.currentTimeMillis() - startTime));
//        checkState(res == Status.UNSATISFIABLE,
//                "formula must be UNSAT for decision template extraction, got: " + res);

        UnsatCoreEnumerator enumerator = new UnsatCoreEnumerator(context, solver, boolConst2Label.keySet());
        ArrayList<DecisionTemplate> dts = new ArrayList<>();
        Optional<Collection<BoolExpr>> core;
        for (int i = 0; i < 2 && (core = enumerator.next()).isPresent(); ++i) {
            ImmutableList<Label> coreLabels = core.get().stream()
                    .map(boolConst2Label::get)
                    .collect(ImmutableList.toImmutableList());
            dts.add(buildDecisionTemplate(coreLabels, allNonValueOperands));
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
