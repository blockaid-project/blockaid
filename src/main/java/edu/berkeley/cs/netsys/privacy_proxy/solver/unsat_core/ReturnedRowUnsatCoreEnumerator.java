package edu.berkeley.cs.netsys.privacy_proxy.solver.unsat_core;

import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.solver.executor.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.PreambleLabel;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.ReturnedRowLabel;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.*;
import com.google.common.collect.*;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.QueryChecker;
import edu.berkeley.cs.netsys.privacy_proxy.solver.*;
import edu.berkeley.cs.netsys.privacy_proxy.util.LogLevel;
import edu.berkeley.cs.netsys.privacy_proxy.util.Options;
import edu.berkeley.cs.netsys.privacy_proxy.util.VampireConfigurations;

import java.util.*;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static edu.berkeley.cs.netsys.privacy_proxy.util.Logger.printMessage;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Logger.printStylizedMessage;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.PRUNE_PREAMBLE;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.PRUNE_PREAMBLE_IN_VALIDATION;
import static edu.berkeley.cs.netsys.privacy_proxy.util.TerminalColor.*;

public class ReturnedRowUnsatCoreEnumerator<CU extends Z3ContextWrapper<?, ?, ?, ?>, CB extends Z3ContextWrapper<?, ?, ?, ?>> {
    private static final int TIMEOUT_S = 20;

    private final QueryChecker checker;
    private final Schema<CB> boundedSchema;
    private final ImmutableList<Policy> policies;
    private final RRLUnsatCoreDeterminacyFormula<CU> rrlFormula;

    private UnsatCoreFormulaBuilder<CB, BoundedInstance<CB>> formulaBuilder = null;
    private Solver solver = null;

    public ReturnedRowUnsatCoreEnumerator(QueryChecker checker, Schema<CU> unboundedSchema, Schema<CB> boundedSchema,
                                          ImmutableList<Policy> policies) {
        this.checker = checker;
        this.boundedSchema = boundedSchema;
        this.policies = policies;
        this.rrlFormula = new RRLUnsatCoreDeterminacyFormula<>(unboundedSchema, policies);
    }

    public record Core(Set<ReturnedRowLabel> rrCore, Set<PreambleLabel> preambleCore) {}

    public Optional<Core> getInitialRRCore(UnmodifiableLinearQueryTrace trace) {
        long startNs = System.nanoTime();
        String smt = rrlFormula.generateUnsatCoreSMT(trace);
        System.out.println("\t\t| Prepare formula:\t" + (System.nanoTime() - startNs) / 1000000);
        checker.printFormula(smt, "rr_unsat_core");

        ArrayList<ProcessSMTExecutor> executors = new ArrayList<>();
        CountDownLatch latch = new CountDownLatch(1);
        // We don't include Z3 because it generates large unsat cores.
//        executors.add(new Z3Executor("z3", smt, latch));
        executors.add(new CVCExecutor("cvc4", "cvc4", smt, latch));
        executors.add(new CVCExecutor("cvc5", "cvc5", smt, latch));
        for (Map.Entry<String, String> entry : VampireConfigurations.getAll(TIMEOUT_S).entrySet()) {
            String configName = entry.getKey(), configString = entry.getValue();
            executors.add(new VampireUCoreExecutor(configName, smt, latch, configString));
        }

        for (SMTExecutor executor : executors) {
            executor.start();
        }

        startNs = System.nanoTime();
        try {
            latch.await(TIMEOUT_S, TimeUnit.SECONDS);
            for (SMTExecutor executor : executors) {
                executor.signalShutdown();
            }
            for (SMTExecutor executor : executors) {
                executor.join();
            }
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }

        Set<ReturnedRowLabel> smallestRRCore = null;
        Set<PreambleLabel> preambleCore = null;
        String winner = null;
        for (ProcessSMTExecutor e : executors) {
            if (e.getResult() != Status.UNSATISFIABLE) {
                continue;
            }

            List<String> unsatCore = Arrays.asList(e.getUnsatCore());
            Set<ReturnedRowLabel> rrCore = rrlFormula.extractRRLabels(unsatCore);
            if (smallestRRCore == null || smallestRRCore.size() > rrCore.size()) {
                winner = e.getName();
                smallestRRCore = rrCore;
                preambleCore = rrlFormula.extractPreambleLabels(unsatCore);
            }
        }
        long solveDurMs = (System.nanoTime() - startNs) / 1000000;
        System.out.println("\t\t| Solve:\t" + solveDurMs);

        if (smallestRRCore == null) {
            return Optional.empty();
        }

        printMessage("Winner:\t" + winner + "\t" + solveDurMs);
        printMessage("\tReturned-row core: " + smallestRRCore);
        if (PRUNE_PREAMBLE == Options.PrunePreambleType.UNSAT_CORE) {
            printMessage("\tPreamble core: " + preambleCore);
        }

        return Optional.of(new Core(smallestRRCore, preambleCore));
    }

    // Returns empty if formula is not determined UNSAT.
    // MUST be called after calling `getInitialRRCore`, which would have "registered" all constants with the context.
    public Set<ReturnedRowLabel> minimizeRRCore(UnmodifiableLinearQueryTrace trace,
                                                Set<ReturnedRowLabel> initialRRCore,
                                                Set<PreambleLabel> preambleCore,
                                                int boundSlack) {
        SubQueryTrace subTrace = trace.getSubTrace(
                initialRRCore.stream()
                        .map(rrl -> new QueryTupleIdxPair(rrl.queryIdx(), rrl.rowIdx()))
                        .collect(ImmutableList.toImmutableList())
        );

        long startNs = System.nanoTime();
        CB boundedContext = boundedSchema.getContext();
        try {
            CountingBoundEstimator<CB> cbe = new CountingBoundEstimator<>();
            UnsatCoreBoundEstimator<CB> boundEstimator = new UnsatCoreBoundEstimator<>(cbe);
            Map<String, Integer> bounds = boundEstimator.calculateBounds(boundedSchema, subTrace);

            Map<String, Integer> slackBounds = Maps.transformValues(bounds, n -> n + boundSlack);

            // For coarse preamble pruning, we don't actually prune the views and dependencies.
            // We keep the entire preamble and instead set the bounds of irrelevant tables to zero.
            // Views and dependencies that rely on irrelevant tables should then result in trivial formulas.
            if (PRUNE_PREAMBLE == Options.PrunePreambleType.COARSE) {
                Set<String> relevantTables = boundedSchema.computeRelevantTables(subTrace);
                printMessage(() -> "Relevant tables:\t" + relevantTables);
                slackBounds = Maps.transformEntries(slackBounds,
                        (table, bound) -> relevantTables.contains(table) ? Objects.requireNonNull(bound) : 0);
            }

            {
                var finalSlackBounds = slackBounds;
                printMessage(() -> "Bounds:\t" + finalSlackBounds, LogLevel.VERBOSE);
            }

            if (PRUNE_PREAMBLE != Options.PrunePreambleType.UNSAT_CORE) {
                preambleCore = null;
            }

            BoundedDeterminacyFormula<CB> baseFormula = new BoundedDeterminacyFormula<>(
                    boundedSchema, policies, slackBounds,
                    true, TextOption.NO_TEXT, null,
                    preambleCore);
            this.formulaBuilder = new UnsatCoreFormulaBuilder<>(baseFormula, policies);
            printMessage("\t\t| Bounded RRL core 1:\t" + (System.nanoTime() - startNs) / 1000000, LogLevel.VERBOSE);

            EnumSet<UnsatCoreFormulaBuilder.Option> options = EnumSet.noneOf(UnsatCoreFormulaBuilder.Option.class);
            if (PRUNE_PREAMBLE_IN_VALIDATION == Options.OnOffType.OFF) {
                options = EnumSet.of(UnsatCoreFormulaBuilder.Option.NO_MARK_BG);
            }
            UnsatCoreFormulaBuilder.Formulas<ReturnedRowLabel, PreambleLabel> fs =
                    formulaBuilder.buildReturnedRowsOnly(subTrace, options);
            solver = boundedContext.mkQfSolver();

            if (subTrace.size() == 1) { // Only the current query is in the trace.  It doesn't depend on any previous!
                // However, only return after making a solver, which is expected by subsequent callers to `getSolver()`.
                return Collections.emptySet();
            }

            printMessage("\t\t| Bounded RRL core 2:\t" + (System.nanoTime() - startNs) / 1000000, LogLevel.VERBOSE);
            try (UnsatCoreEnumerator<ReturnedRowLabel, PreambleLabel, CB> uce
                         = new UnsatCoreEnumerator<>(boundedContext, solver, fs, Order.ARBITRARY, true)) {
                printMessage("\t\t| Bounded RRL core 3:\t" + (System.nanoTime() - startNs) / 1000000, LogLevel.VERBOSE);
                Set<ReturnedRowLabel> s = uce.next().get();
                printMessage("\t\t| Bounded RRL core 4:\t" + (System.nanoTime() - startNs) / 1000000, LogLevel.VERBOSE);
                s = s.stream().map(l -> (ReturnedRowLabel) DecisionTemplateGenerator.backMapLabel(l, subTrace)).collect(Collectors.toSet());
                return s;
            }
        } finally {
            printMessage("\t\t| Bounded RRL core:\t" + (System.nanoTime() - startNs) / 1000000);
        }
    }

    // MUST be called only after `minimizeRRCore`.
    public UnsatCoreFormulaBuilder<CB, BoundedInstance<CB>> getFormulaBuilder() {
        return Objects.requireNonNull(formulaBuilder);
    }

    // MUST be called only after `minimizeRRCore`.
    public Solver getSolver() {
        return Objects.requireNonNull(solver);
    }
}
