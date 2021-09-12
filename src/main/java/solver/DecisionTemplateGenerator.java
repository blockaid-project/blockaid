package solver;

import cache.DecisionTemplate;
import solver.labels.*;
import cache.trace.*;
import solver.unsat_core.Order;
import solver.unsat_core.ReturnedRowUnsatCoreEnumerator;
import solver.unsat_core.UnsatCoreEnumerator;
import com.google.common.collect.*;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import policy_checker.Policy;
import policy_checker.QueryChecker;
import util.UnionFind;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static util.TerminalColor.*;

public class DecisionTemplateGenerator {
    private final Schema schema;
    private final ReturnedRowUnsatCoreEnumerator rruce;
    private final UnsatCoreFormulaBuilder unboundedUcBuilder;
    private final SMTPortfolioRunner runner;

    public DecisionTemplateGenerator(QueryChecker checker, Schema schema, Collection<Policy> policies,
                                     Collection<Query> views, DeterminacyFormula unboundedFormula) {
        this.schema = schema;
        this.rruce = new ReturnedRowUnsatCoreEnumerator(checker, schema, policies, views);
        this.unboundedUcBuilder = new UnsatCoreFormulaBuilder(unboundedFormula, policies);
        this.runner = new SMTPortfolioRunner(checker, QueryChecker.SOLVE_TIMEOUT_MS);
    }

    // Returns empty if formula is not determined UNSAT.
    public Optional<Collection<DecisionTemplate>> generate(UnmodifiableLinearQueryTrace trace) {
        // Step 1: Find all minimal unsat cores among the returned-row labels, assuming all equalities hold.
        Optional<Set<ReturnedRowLabel>> oCore = rruce.getOne(trace);
        if (oCore.isEmpty()) {
            return Optional.empty();
        }
        Collection<Collection<ReturnedRowLabel>> rrCores = List.of(oCore.get());
        System.out.println(ANSI_BLUE_BACKGROUND + ANSI_RED + rrCores + ANSI_RESET);

        // Step 2: For each unsat core among query labels, enumerate unsat cores among equality labels.
        // Reusing the bounde formula builder to avoid making the bounded formula again.
        UnsatCoreFormulaBuilder boundedUcBuilder = rruce.getFormulaBuilder();

        MyZ3Context context = schema.getContext();
        ArrayList<DecisionTemplate> dts = new ArrayList<>();
        for (Collection<ReturnedRowLabel> rrCore : rrCores) {
            ImmutableList<QueryTupleIdxPair> toKeep = rrCore.stream()
                    .map(rrl -> new QueryTupleIdxPair(rrl.getQueryIdx(), rrl.getRowIdx()))
                    .collect(ImmutableList.toImmutableList());
            SubQueryTrace sqt = trace.getSubTrace(toKeep);

            // Build "param relations only" unsat core formula, i.e., assumes the entire trace is present.
            context.startTrackingConsts();
            UnsatCoreFormulaBuilder.Formulas<Label> fs = boundedUcBuilder.buildParamRelationsOnly(sqt);
            ImmutableSet<Operand> allOperandsOld =
                    fs.getLabeledExprs().keySet().stream() // Get all labels.
                            .flatMap(l -> l.getOperands().stream()) // Gather both operands of each label.
                            .map(o -> backMapOperand(o, sqt))
                            .collect(ImmutableSet.toImmutableSet());

            Solver solver = context.mkSolver(context.mkSymbol("QF_UF"));
            solver.add(fs.getBackground().toArray(new BoolExpr[0]));

            Map<Label, BoolExpr> labeledExprs = fs.getLabeledExprs();
            Set<Label> paramsCore;
            try (UnsatCoreEnumerator<Label> uce =
                         new UnsatCoreEnumerator<>(context, solver, labeledExprs, Order.INCREASING)) {
                System.out.println("total    #labels =\t" + labeledExprs.size());
                Set<Label> startingUnsatCore = uce.getStartingUnsatCore();
                System.out.println("starting #labels =\t" + startingUnsatCore.size());

                long startMs = System.currentTimeMillis();
                Solver thisSolver = context.mkSolver();
                for (Label l : startingUnsatCore) {
                    thisSolver.add(labeledExprs.get(l));
                }
                Set<Label> consequence = new HashSet<>();
                for (Map.Entry<Label, BoolExpr> entry : labeledExprs.entrySet()) {
                    Label l = entry.getKey();
                    if (startingUnsatCore.contains(l)
                            || thisSolver.check(context.mkNot(entry.getValue())) == Status.UNSATISFIABLE) {
                        consequence.add(l);
                    }
                }
                System.out.println("conseq   #labels =\t" + consequence.size());
                uce.restrictTo(consequence);
//                    uce.optimizeCritical();
                System.out.println("\t\t| Find conseq:\t" + (System.currentTimeMillis() - startMs));

                paramsCore = uce.next().get();
            }
            context.stopTrackingConsts();
            System.out.println("final #labels =\t" + paramsCore.size());

            // Step 3: Validate the unsat core on unbounded formula.
            System.out.println("\t\t| Validate:");
            String validateSMT = unboundedUcBuilder.buildValidateParamRelationsOnlySMT(sqt, paramsCore);
            checkState(runner.checkFastUnsatFormula(validateSMT, "validate"));

            // Step 4: Make decision tempalte.
            List<Label> coreLabelsOld = paramsCore.stream().map(l -> backMapLabel(l, sqt))
                    .collect(Collectors.toList());
            // `rrCore` is with respect to the old (complete) trace, so no need to back map it.
            coreLabelsOld.addAll(rrCore);
            dts.add(buildDecisionTemplate(trace, coreLabelsOld, allOperandsOld));
        }

        return Optional.of(dts);
    }

    public static Operand backMapOperand(Operand o, SubQueryTrace sqt) {
        switch (o.getKind()) {
            case CONTEXT_CONSTANT:
            case VALUE:
                return o;
            case QUERY_PARAM:
                QueryParamOperand qpo = (QueryParamOperand) o;
                if (qpo.isCurrentQuery()) {
                    return qpo;
                }
                int oldQueryIdx = sqt.getQueryIdxBackMap().get(qpo.getQueryIdx());
                return new QueryParamOperand(oldQueryIdx, false, qpo.getParamIdx());
            case RETURNED_ROW_ATTR:
                ReturnedRowFieldOperand rrfo = (ReturnedRowFieldOperand) o;
                QueryTupleIdxPair old = sqt.getBackMap().get(
                        new QueryTupleIdxPair(rrfo.getQueryIdx(), rrfo.getReturnedRowIdx()));
                return new ReturnedRowFieldOperand(old.getQueryIdx(), old.getTupleIdx(), rrfo.getColIdx());
        }
        checkArgument(false, "invalid operand kind: " + o.getKind());
        return null;
    }

    public static Label backMapLabel(Label l, SubQueryTrace sqt) {
        switch (l.getKind()) {
            case EQUALITY:
                EqualityLabel el = (EqualityLabel) l;
                return new EqualityLabel(backMapOperand(el.getLhs(), sqt), backMapOperand(el.getRhs(), sqt));
            case LESS_THAN:
                LessThanLabel ltl = (LessThanLabel) l;
                return new LessThanLabel(backMapOperand(ltl.getLhs(), sqt), backMapOperand(ltl.getRhs(), sqt));
            case RETURNED_ROW:
                ReturnedRowLabel rrl = (ReturnedRowLabel) l;
                QueryTupleIdxPair old = sqt.getBackMap().get(new QueryTupleIdxPair(rrl.getQueryIdx(), rrl.getRowIdx()));
                return new ReturnedRowLabel(old.getQueryIdx(), old.getTupleIdx());
        }
        checkArgument(false, "invalid label kind: " + l.getKind());
        return null;
    }

    private DecisionTemplate buildDecisionTemplate(UnmodifiableLinearQueryTrace trace,
                                                   List<Label> unsatCore, Set<Operand> allOperands) {
//        System.out.println(ANSI_RED + ANSI_BLUE_BACKGROUND + unsatCore + ANSI_RESET);

        // Find all equivalence classes of operands.
        UnionFind<Operand> uf = new UnionFind<>(allOperands);
        for (Label l : unsatCore) {
            if (l.getKind() != Label.Kind.EQUALITY) {
                continue;
            }

            EqualityLabel el = (EqualityLabel) l;
            uf.union(el.getLhs(), el.getRhs());
        }

        // If an equivalence class is equal to a value, attach the value as data in the union-find.
        for (Operand o : allOperands) {
            if (o.getKind() != Operand.Kind.VALUE) {
                continue;
            }
            uf.attachData(o, ((ValueOperand) o).getValue());
        }

        Set<Operand> rootsUsedInLessThan = unsatCore.stream()
                .filter(l -> l.getKind() == Label.Kind.LESS_THAN)
                .flatMap(l -> l.getOperands().stream())
                .map(uf::find)
                .collect(Collectors.toSet());

        checkArgument(rootsUsedInLessThan.stream().allMatch(o -> uf.findComplete(o).getDatum() == null),
                "currently unsupported: less than with value as operand");

        // Assign consecutive indexes (starting from 0) to roots, excluding those with only one element (unless it's
        // used in a less-than) and those with a concrete value attached.
        Map<Operand, Integer> root2Index = new HashMap<>();
        for (Operand root : uf.getRoots()) {
            UnionFind<Operand>.EquivalenceClass ec = uf.findComplete(root);
            if (ec.getDatum() == null && (ec.getSize() >= 2 || rootsUsedInLessThan.contains(ec.getRoot()))) {
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

        // Record equivalence classes.
        for (Operand o : allOperands) {
            if (o.getKind() == Operand.Kind.VALUE) {
                continue;
            }

            UnionFind<Operand>.EquivalenceClass ec = uf.findComplete(o);
            Object datum = ec.getDatum();
            Integer rootIndex = root2Index.get(ec.getRoot());
            if (rootIndex == null && datum == null) { // This operand has no constraints on it.
                continue;
            }

            switch (o.getKind()) {
                case CONTEXT_CONSTANT:
                    String constName = ((ContextConstantOperand) o).getName();
                    if (datum == null) {
                        constName2ECBuilder.put(constName, rootIndex);
                    } else {
                        constName2ValueBuilder.put(constName, datum);
                    }
                    break;
                case QUERY_PARAM:
                    QueryParamOperand qpo = (QueryParamOperand) o;
                    // Set param for all entry builder(s) for this query.
                    Collection<DecisionTemplate.EntryBuilder> ebs =
                            qpo.isCurrentQuery() ? List.of(currEB) :
                                    queryIdx2rowEBs.getOrDefault(qpo.getQueryIdx(), Collections.emptyMap())
                                            .values();
                    // If the query index is not in `queryIdx2rowEBs`, the query is irrelevant and so we ignore.
                    ebs.forEach(
                            datum == null ?
                                    eb -> eb.setParamEC(qpo.getParamIdx(), rootIndex) :
                                    eb -> eb.setParamValue(qpo.getParamIdx(), datum)
                    );
                    break;
                case RETURNED_ROW_ATTR:
                    ReturnedRowFieldOperand rrfo = (ReturnedRowFieldOperand) o;
                    Map<Integer, DecisionTemplate.EntryBuilder> rowEBs = queryIdx2rowEBs.get(rrfo.getQueryIdx());
                    if (rowEBs == null) { // This query is irrelevant.
                        break;
                    }
                    DecisionTemplate.EntryBuilder eb = rowEBs.get(rrfo.getReturnedRowIdx());
                    if (eb == null) { // This returned row is irrelevant.
                        break;
                    }
                    if (datum == null) {
                        eb.setRowAttrEC(rrfo.getColIdx(), rootIndex);
                    } else {
                        eb.setRowAttrValue(rrfo.getColIdx(), datum);
                    }
                    break;
                default:
                    checkState(false, "unexpected operand: " + o);
            }
        }

        ArrayList<DecisionTemplate.LessThan> lts = new ArrayList<>();
        for (Label l : unsatCore) {
            if (l.getKind() != Label.Kind.LESS_THAN) {
                continue;
            }
            LessThanLabel ltl = (LessThanLabel) l;
            int lhsIndex = root2Index.get(uf.find(ltl.getLhs())), rhsIndex = root2Index.get(uf.find(ltl.getRhs()));
            lts.add(new DecisionTemplate.LessThan(lhsIndex, rhsIndex));
        }

        ImmutableList.Builder<DecisionTemplate.Entry> entriesBuilder = new ImmutableList.Builder<>();
        entriesBuilder.add(currEB.build());
        for (Map<Integer, DecisionTemplate.EntryBuilder> rowEBs : queryIdx2rowEBs.values()) {
            for (DecisionTemplate.EntryBuilder eb : rowEBs.values()) {
                entriesBuilder.add(eb.build());
            }
        }
        return new DecisionTemplate(
                entriesBuilder.build(), constName2ECBuilder.build(), constName2ValueBuilder.build(), lts
        );
    }
}
