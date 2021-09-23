package solver;

import cache.DecisionTemplate;
import com.microsoft.z3.*;
import solver.context.MyZ3Context;
import solver.labels.*;
import cache.trace.*;
import solver.unsat_core.Order;
import solver.unsat_core.ReturnedRowUnsatCoreEnumerator;
import solver.unsat_core.UnsatCoreEnumerator;
import com.google.common.collect.*;
import policy_checker.Policy;
import policy_checker.QueryChecker;
import util.Logger;
import util.UnionFind;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static util.Logger.printMessage;
import static util.TerminalColor.*;

public class DecisionTemplateGenerator {
    private final Schema schema;
    private final ReturnedRowUnsatCoreEnumerator rruce;
    private final UnsatCoreFormulaBuilder unboundedUcBuilder;
    private final SMTPortfolioRunner runner;

    public DecisionTemplateGenerator(QueryChecker checker, Schema schema, Collection<Policy> policies,
                                     List<Query> views, DeterminacyFormula unboundedFormula) {
        this.schema = schema;
        this.rruce = new ReturnedRowUnsatCoreEnumerator(checker, schema, policies, views);
        this.unboundedUcBuilder = new UnsatCoreFormulaBuilder(unboundedFormula, policies);
        this.runner = new SMTPortfolioRunner(checker, QueryChecker.SOLVE_TIMEOUT_MS);
    }

    // Returns empty if formula is not determined UNSAT.
    public Optional<Collection<DecisionTemplate>> generate(UnmodifiableLinearQueryTrace trace) {
        // Step 1: Find all minimal unsat cores among the returned-row labels, assuming all equalities hold.
        Optional<ReturnedRowUnsatCoreEnumerator.Core> oCore = rruce.getInitialRRCore(trace);
        if (oCore.isEmpty()) {
            return Optional.empty();
        }

        for (int slack = 1; slack <= 3; ++slack) {
            ReturnedRowUnsatCoreEnumerator.Core core = oCore.get();
            Optional<DecisionTemplate> odt = generate(trace, core.rrCore(), core.preambleCore(), slack);
            if (odt.isPresent()) {
                return Optional.of(List.of(odt.get()));
            }
        }

        return Optional.empty();
    }

    private Optional<DecisionTemplate> generate(UnmodifiableLinearQueryTrace trace,
                                                Set<ReturnedRowLabel> initialRRCore,
                                                Set<PreambleLabel> preambleCore,
                                                int boundSlack) {
        Set<ReturnedRowLabel> rrCore = rruce.minimizeRRCore(trace, initialRRCore, preambleCore, boundSlack);
//        System.out.println(ANSI_BLUE_BACKGROUND + ANSI_RED + initialRRCore + ANSI_RESET);

        // Step 2: For each unsat core among query labels, enumerate unsat cores among equality labels.
        // Reusing the bounded formula builder to avoid making the bounded formula again.
        UnsatCoreFormulaBuilder boundedUcBuilder = rruce.getFormulaBuilder();

        MyZ3Context context = schema.getContext();
        ImmutableList<QueryTupleIdxPair> toKeep = rrCore.stream()
                .map(rrl -> new QueryTupleIdxPair(rrl.queryIdx(), rrl.rowIdx()))
                .collect(ImmutableList.toImmutableList());
        SubQueryTrace sqt = trace.getSubTrace(toKeep);

        // Build "param relations only" unsat core formula, i.e., assumes the entire trace is present.
        context.startTrackingConsts();
        UnsatCoreFormulaBuilder.Formulas<Label> fs = boundedUcBuilder.buildParamRelationsOnly(sqt);
//                UnsatCoreFormulaBuilder.Option.POSITIVE);
        ImmutableSet<Operand> allOperandsOld =
                fs.getLabeledExprs().keySet().stream() // Get all labels.
                        .flatMap(l -> l.getOperands().stream()) // Gather both operands of each label.
                        .map(o -> backMapOperand(o, sqt))
                        .collect(ImmutableSet.toImmutableSet());

        Solver solver = rruce.getSolver();

//        Set<Label> paramsCore;
//        try (FindMinimalSat fms = new FindMinimalSat(context, solver)) {
//            paramsCore = fms.compute(fs);
//        }

        solver.add(fs.getBackground().toArray(new BoolExpr[0]));

        Map<Label, BoolExpr> labeledExprs = fs.getLabeledExprs();
        Set<Label> paramsCore;
        try (UnsatCoreEnumerator<Label> uce =
                     new UnsatCoreEnumerator<>(context, solver, labeledExprs, Order.INCREASING)) {
            printMessage("total    #labels =\t" + labeledExprs.size());
            Set<Label> startingUnsatCore = uce.getStartingUnsatCore();
            printMessage("starting #labels =\t" + startingUnsatCore.size() + "\t" + startingUnsatCore);

            long startNs = System.nanoTime();
            // Seems sketchy to mess with the solver when it's being "owned" by `uce`.
            solver.push();
            for (Label l : startingUnsatCore) {
                solver.add(labeledExprs.get(l));
            }
            Set<Label> consequence = new HashSet<>();
            for (Map.Entry<Label, BoolExpr> entry : labeledExprs.entrySet()) {
                Label l = entry.getKey();
                if (startingUnsatCore.contains(l)
                        || solver.check(context.mkNot(entry.getValue())) == Status.UNSATISFIABLE) {
                    consequence.add(l);
                }
            }
            solver.pop();
            printMessage("conseq   #labels =\t" + consequence.size()); // + "\t" + consequence);
            uce.restrictTo(consequence);
//                    uce.optimizeCritical();
            printMessage("\t\t| Find conseq:\t" + (System.nanoTime() - startNs) / 1e6);

            paramsCore = uce.next().get();
        }
        context.stopTrackingConsts();
        printMessage("final #labels =\t" + paramsCore.size() + "\t" + paramsCore);

        // Step 4: Make decision template.
        List<Label> coreLabelsOld = paramsCore.stream().map(l -> backMapLabel(l, sqt)).collect(Collectors.toList());
        // `rrCore` is with respect to the old (complete) trace, so no need to back map it.
        coreLabelsOld.addAll(rrCore);
        DecisionTemplate dt = buildDecisionTemplate(trace, coreLabelsOld, allOperandsOld);

        // Step 3: Validate the unsat core on unbounded formula.
        System.out.println("\t\t| Validate:");
        String validateSMT = unboundedUcBuilder.buildValidateParamRelationsOnlySMT(sqt, paramsCore);
        if (!runner.checkFastUnsatFormula(validateSMT, "validate")) {
            Logger.printStylizedMessage("validation failed (slack = " + boundSlack + ")", ANSI_RED_BACKGROUND);
            System.out.println(dt);
            System.out.println(coreLabelsOld);
            return Optional.empty();
        }

        return Optional.of(dt);
    }

    public static Operand backMapOperand(Operand o, SubQueryTrace sqt) {
        return switch (o.getKind()) {
            case CONTEXT_CONSTANT:
            case VALUE:
                yield o;
            case QUERY_PARAM:
                QueryParamOperand qpo = (QueryParamOperand) o;
                if (qpo.isCurrentQuery()) {
                    yield qpo;
                }
                int oldQueryIdx = sqt.getQueryIdxBackMap().get(qpo.queryIdx());
                yield new QueryParamOperand(oldQueryIdx, false, qpo.paramIdx());
            case RETURNED_ROW_ATTR:
                ReturnedRowFieldOperand rrfo = (ReturnedRowFieldOperand) o;
                QueryTupleIdxPair old = sqt.getBackMap().get(
                        new QueryTupleIdxPair(rrfo.queryIdx(), rrfo.returnedRowIdx()));
                yield new ReturnedRowFieldOperand(old.queryIdx(), old.tupleIdx(), rrfo.colIdx());
        };
    }

    public static Label backMapLabel(Label l, SubQueryTrace sqt) {
        return switch (l.getKind()) {
            case EQUALITY -> {
                EqualityLabel el = (EqualityLabel) l;
                yield new EqualityLabel(backMapOperand(el.lhs(), sqt), backMapOperand(el.rhs(), sqt));
            }
            case LESS_THAN -> {
                LessThanLabel ltl = (LessThanLabel) l;
                yield new LessThanLabel(backMapOperand(ltl.lhs(), sqt), backMapOperand(ltl.rhs(), sqt));
            }
            case RETURNED_ROW -> {
                ReturnedRowLabel rrl = (ReturnedRowLabel) l;
                QueryTupleIdxPair old = sqt.getBackMap().get(new QueryTupleIdxPair(rrl.queryIdx(), rrl.rowIdx()));
                yield new ReturnedRowLabel(old.queryIdx(), old.tupleIdx());
            }
        };
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
            uf.union(el.lhs(), el.rhs());
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
            int queryIdx = rrl.queryIdx();

            Map<Integer, DecisionTemplate.EntryBuilder> rowEBs =
                    queryIdx2rowEBs.computeIfAbsent(queryIdx, k -> new HashMap<>());

            int rowIdx = rrl.rowIdx();
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
                case CONTEXT_CONSTANT -> {
                    String constName = ((ContextConstantOperand) o).name();
                    if (datum == null) {
                        constName2ECBuilder.put(constName, rootIndex);
                    } else {
                        constName2ValueBuilder.put(constName, datum);
                    }
                }
                case QUERY_PARAM -> {
                    QueryParamOperand qpo = (QueryParamOperand) o;
                    // Set param for all entry builder(s) for this query.
                    Collection<DecisionTemplate.EntryBuilder> ebs =
                            qpo.isCurrentQuery() ? List.of(currEB) :
                                    queryIdx2rowEBs.getOrDefault(qpo.queryIdx(), Collections.emptyMap())
                                            .values();
                    // If the query index is not in `queryIdx2rowEBs`, the query is irrelevant and so we ignore.
                    ebs.forEach(
                            datum == null ?
                                    eb -> eb.setParamEC(qpo.paramIdx(), rootIndex) :
                                    eb -> eb.setParamValue(qpo.paramIdx(), datum)
                    );
                }
                case RETURNED_ROW_ATTR -> {
                    ReturnedRowFieldOperand rrfo = (ReturnedRowFieldOperand) o;
                    Map<Integer, DecisionTemplate.EntryBuilder> rowEBs = queryIdx2rowEBs.get(rrfo.queryIdx());
                    if (rowEBs == null) { // This query is irrelevant.
                        break;
                    }
                    DecisionTemplate.EntryBuilder eb = rowEBs.get(rrfo.returnedRowIdx());
                    if (eb == null) { // This returned row is irrelevant.
                        break;
                    }
                    if (datum == null) {
                        eb.setRowAttrEC(rrfo.colIdx(), rootIndex);
                    } else {
                        eb.setRowAttrValue(rrfo.colIdx(), datum);
                    }
                }
                default -> throw new IllegalArgumentException("unexpected operand: " + o);
            }
        }

        ArrayList<DecisionTemplate.LessThan> lts = new ArrayList<>();
        for (Label l : unsatCore) {
            if (l.getKind() != Label.Kind.LESS_THAN) {
                continue;
            }
            LessThanLabel ltl = (LessThanLabel) l;
            int lhsIndex = root2Index.get(uf.find(ltl.lhs())), rhsIndex = root2Index.get(uf.find(ltl.rhs()));
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
