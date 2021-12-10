package edu.berkeley.cs.netsys.privacy_proxy.solver;

import edu.berkeley.cs.netsys.privacy_proxy.cache.DecisionTemplate;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.*;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.unsat_core.Order;
import edu.berkeley.cs.netsys.privacy_proxy.solver.unsat_core.ReturnedRowUnsatCoreEnumerator;
import edu.berkeley.cs.netsys.privacy_proxy.solver.unsat_core.UnsatCoreEnumerator;
import com.google.common.collect.*;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.QueryChecker;
import edu.berkeley.cs.netsys.privacy_proxy.util.Options;
import edu.berkeley.cs.netsys.privacy_proxy.util.UnionFind;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Logger.printMessage;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Logger.printStylizedMessage;
import static edu.berkeley.cs.netsys.privacy_proxy.util.TerminalColor.*;

public class DecisionTemplateGenerator<CU extends Z3ContextWrapper<?, ?, ?, ?>, CB extends Z3ContextWrapper<?, ?, ?, ?>> {
    private final QueryChecker checker;
    private final Schema<CU> unboundedSchema;
    private final Schema<CB> boundedSchema;
    private final ReturnedRowUnsatCoreEnumerator<CU, CB> rruce;
    private final UnsatCoreFormulaBuilder<CU, Instance<CU>> unboundedUcBuilder;
    private final SMTPortfolioRunner runner;

    public DecisionTemplateGenerator(QueryChecker checker, Schema<CU> unboundedSchema, Schema<CB> boundedSchema,
                                     ImmutableList<Policy> policies, DeterminacyFormula<CU, Instance<CU>> unboundedFormula) {
        this.checker = checker;
        this.unboundedSchema = unboundedSchema;
        this.boundedSchema = boundedSchema;
        this.rruce = new ReturnedRowUnsatCoreEnumerator<>(checker, unboundedSchema, boundedSchema, policies);
        this.unboundedUcBuilder = new UnsatCoreFormulaBuilder<>(unboundedFormula, policies);
        this.runner = new SMTPortfolioRunner(checker, Options.SOLVE_TIMEOUT_MS);
    }

    // Returns empty if formula is not determined UNSAT.
    public Optional<Collection<DecisionTemplate>> generate(UnmodifiableLinearQueryTrace trace) {
        CU unboundedContext = unboundedSchema.getContext();
        CB boundedContext = boundedSchema.getContext();
        unboundedContext.push();
        boundedContext.push();
        try {
            // Step 1: Find one minimal unsat cores among the returned-row labels, assuming all equalities hold.
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
        } finally {
            boundedContext.pop();
            unboundedContext.pop();
        }
    }

    private Optional<DecisionTemplate> generate(UnmodifiableLinearQueryTrace trace,
                                                Set<ReturnedRowLabel> initialRRCore,
                                                Set<PreambleLabel> preambleCore,
                                                int boundSlack) {
        Set<ReturnedRowLabel> rrCore = rruce.minimizeRRCore(trace, initialRRCore, preambleCore, boundSlack);
        printStylizedMessage(rrCore::toString, ANSI_BLUE_BACKGROUND + ANSI_RED);

        // Step 2: For each unsat core among query labels, enumerate unsat cores among equality labels.
        // Reusing the bounded formula builder to avoid making the bounded formula again.
        UnsatCoreFormulaBuilder<CB, BoundedInstance<CB>> boundedUcBuilder = rruce.getFormulaBuilder();

        CB boundedContext = boundedSchema.getContext();
        ImmutableList<QueryTupleIdxPair> toKeep = rrCore.stream()
                .map(rrl -> new QueryTupleIdxPair(rrl.queryIdx(), rrl.rowIdx()))
                .collect(ImmutableList.toImmutableList());
        SubQueryTrace sqt = trace.getSubTrace(toKeep);

        // Build "param relations only" unsat core formula, i.e., assumes the entire trace is present.
        UnsatCoreFormulaBuilder.Formulas<Label, PreambleLabel> fs = boundedUcBuilder.buildParamRelationsOnly(
                sqt,
                Options.PRUNE_PREAMBLE_IN_VALIDATION == Options.OnOffType.OFF
                        ? EnumSet.of(UnsatCoreFormulaBuilder.Option.NO_MARK_BG)
                        : EnumSet.noneOf(UnsatCoreFormulaBuilder.Option.class)
        );
        ImmutableSet<Operand> allOperandsOld =
                fs.labeledExprs().keySet().stream() // Get all labels.
                        .flatMap(l -> l.getOperands().stream()) // Gather both operands of each label.
                        .map(o -> backMapOperand(o, sqt))
                        .collect(ImmutableSet.toImmutableSet());

        long startNs = System.nanoTime();
        Solver solver = rruce.getSolver();

        Set<Label> smallestParamsCore;
        Set<PreambleLabel> minimalPreambleCore = null; // This should be minimal _given_ the smallest params core.

        // If we don't have preamble labels in the formula, let the solver minimize unsat cores
        // (consisting solely of param labels).
        ImmutableSet<UnsatCoreEnumerator.Option> enumeratorOptions =
                Options.PRUNE_PREAMBLE_IN_VALIDATION == Options.OnOffType.OFF
                        ? Sets.immutableEnumSet(UnsatCoreEnumerator.Option.SOLVER_MINIMIZE_CORE)
                        : ImmutableSet.of();
        try (UnsatCoreEnumerator<Label, PreambleLabel, CB> uce =
                     new UnsatCoreEnumerator<>(boundedContext, solver, fs, Order.INCREASING, enumeratorOptions)) {
            printMessage("Enumerator creation:\t" + (System.nanoTime() - startNs) / 1_000_000 + " ms");
            checker.printFormula(solver::toString, "bg");

            Map<Label, BoolExpr> labeledExprs = fs.labeledExprs();
            printMessage("total    #labels =\t" + labeledExprs.size());
            Set<Label> startingUnsatCore = uce.getStartingUnsatCore();
            printMessage("starting #labels =\t" + startingUnsatCore.size() + "\t" + startingUnsatCore);

            startNs = System.nanoTime();
            Solver thisSolver = boundedContext.mkSolver();
            for (Label l : startingUnsatCore) {
                thisSolver.add(labeledExprs.get(l));
            }

            Set<Label> consequence = new HashSet<>();
            for (Map.Entry<Label, BoolExpr> entry : labeledExprs.entrySet()) {
                Label l = entry.getKey();
                if (startingUnsatCore.contains(l)
                        || thisSolver.check(boundedContext.mkNot(entry.getValue())) == Status.UNSATISFIABLE) {
                    consequence.add(l);
                }
            }
            printMessage("conseq   #labels =\t" + consequence.size());  // + "\t" + consequence);
            uce.restrictTo(consequence);
//                    uce.optimizeCritical();
            printMessage("\t\t| Find conseq:\t" + (System.nanoTime() - startNs) / 1e6);

            startNs = System.nanoTime();
            Optional<Set<Label>> oParamsCore = uce.next();
            checkState(oParamsCore.isPresent(), "formula should be unsat");
            smallestParamsCore = oParamsCore.get();

            if (Options.PRUNE_PREAMBLE_IN_VALIDATION == Options.OnOffType.ON) {
                minimalPreambleCore = uce.getUnsatCorePreamble();
            }
            printMessage("\t\t| Find smallest unsat core:\t" + (System.nanoTime() - startNs) / 1_000_000 + " ms");
        }
        printMessage("final #labels =\t" + smallestParamsCore.size() + "\t" + smallestParamsCore);
        if (minimalPreambleCore != null) {
            printMessage("preamble core =\t" + minimalPreambleCore.size() + "\t" + minimalPreambleCore);
        }

        // Step 3: Make decision template.
        List<Label> coreLabelsOld = smallestParamsCore.stream().map(l -> backMapLabel(l, sqt)).collect(Collectors.toList());
        // `rrCore` is with respect to the old (complete) trace, so no need to back map it.
        coreLabelsOld.addAll(rrCore);
        DecisionTemplate dt = buildDecisionTemplate(trace, coreLabelsOld, allOperandsOld);

        // Step 4: Validate the decision template using unbounded formula.
        printMessage("\t\t| Validate:");
        String validateSMT = unboundedUcBuilder.buildValidateParamRelationsOnlySMT(sqt, smallestParamsCore, minimalPreambleCore);
        if (!runner.checkFastUnsatFormula(validateSMT, "validate")) {
            printStylizedMessage("validation failed (slack = " + boundSlack + ")", ANSI_RED_BACKGROUND);
            printMessage(dt.toString());
            printMessage(coreLabelsOld.toString());
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

        checkArgument(rootsUsedInLessThan.stream().noneMatch(o -> uf.findComplete(o).hasDatum()),
                "currently unsupported: less than with value as operand");

        // Assign consecutive indexes (starting from 0) to roots, excluding those with only one element (unless it's
        // used in a less-than) and those with a concrete value attached.
        Map<Operand, Integer> root2Index = new HashMap<>();
        for (Operand root : uf.getRoots()) {
            UnionFind<Operand>.EquivalenceClass ec = uf.findComplete(root);
            if (!ec.hasDatum() && (ec.getSize() >= 2 || rootsUsedInLessThan.contains(ec.getRoot()))) {
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
            if (rootIndex == null && !ec.hasDatum()) { // This operand has no constraints on it.
                continue;
            }

            switch (o.getKind()) {
                case CONTEXT_CONSTANT -> {
                    String constName = ((ContextConstantOperand) o).name();
                    if (!ec.hasDatum()) {
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
                            !ec.hasDatum() ?
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
                    if (!ec.hasDatum()) {
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
