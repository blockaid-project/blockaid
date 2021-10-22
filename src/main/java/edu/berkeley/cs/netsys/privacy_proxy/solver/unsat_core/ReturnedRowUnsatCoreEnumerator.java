package edu.berkeley.cs.netsys.privacy_proxy.solver.unsat_core;

import edu.berkeley.cs.netsys.privacy_proxy.solver.DecisionTemplateGenerator;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.MyZ3Context;
import edu.berkeley.cs.netsys.privacy_proxy.solver.executor.CVC4Executor;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.PreambleLabel;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.ReturnedRowLabel;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.*;
import com.google.common.collect.*;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.QueryChecker;
import edu.berkeley.cs.netsys.privacy_proxy.solver.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.executor.ProcessSMTExecutor;
import edu.berkeley.cs.netsys.privacy_proxy.solver.executor.SMTExecutor;
import edu.berkeley.cs.netsys.privacy_proxy.solver.executor.VampireUCoreExecutor;

import java.util.*;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static edu.berkeley.cs.netsys.privacy_proxy.util.Logger.printMessage;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Logger.printStylizedMessage;
import static edu.berkeley.cs.netsys.privacy_proxy.util.TerminalColor.*;

public class ReturnedRowUnsatCoreEnumerator {
    private static final int TIMEOUT_S = 20;

    private final QueryChecker checker;
    private final Schema schema;
    private final Collection<Policy> policies;
    private final Collection<Query> views;
    private final RRLUnsatCoreDeterminacyFormula rrlFormula;

    private UnsatCoreFormulaBuilder formulaBuilder = null;
    private Solver solver = null;

    public ReturnedRowUnsatCoreEnumerator(QueryChecker checker, Schema schema, Collection<Policy> policies,
                                          List<Query> views) {
        this.checker = checker;
        this.schema = schema;
        this.policies = policies;
        this.views = views;
        this.rrlFormula = new RRLUnsatCoreDeterminacyFormula(schema, views);
    }

    public record Core(Set<ReturnedRowLabel> rrCore, Set<PreambleLabel> preambleCore) {}

    public Optional<Core> getInitialRRCore(UnmodifiableLinearQueryTrace trace) {
        long startNs = System.nanoTime();
        String smt = rrlFormula.generateUnsatCoreSMT(trace);
        System.out.println("\t\t| Prepare formula:\t" + (System.nanoTime() - startNs) / 1000000);

        ArrayList<ProcessSMTExecutor> executors = new ArrayList<>();
        CountDownLatch latch = new CountDownLatch(1);
        executors.add(new CVC4Executor("cvc4", smt, latch));
        executors.add(new VampireUCoreExecutor("vampire_lrs+10_1", smt, latch, "lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_" + (TIMEOUT_S * 10)));
//        executors.add(new VampireUCoreExecutor("vampire_lrs+1_3", smt, latch, "lrs+1_3:2_afr=on:afp=100000:afq=1.0:anc=all_dependent:cond=on:fde=none:gs=on:inw=on:ile=on:irw=on:nm=6:nwc=1:stl=30:sos=theory:updr=off:uhcvi=on_" + (TIMEOUT_S * 10)));
        executors.add(new VampireUCoreExecutor("vampire_dis+11_3", smt, latch, "dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_" + (TIMEOUT_S * 10)));
        executors.add(new VampireUCoreExecutor("vampire_dis+3_1", smt, latch, "dis+3_1_cond=on:fde=unused:nwc=1:sd=1:ss=axioms:st=1.2:sos=on:sac=on:add=off:afp=40000:afq=1.4:anc=none_" + (TIMEOUT_S * 10)));
//        executors.add(new VampireUCoreExecutor("vampire_dis+2_3", smt, latch, "dis+2_3_av=off:cond=on:fsr=off:lcm=reverse:lma=on:nwc=1:sos=on:sp=reverse_arity_" + (TIMEOUT_S * 10)));

//            executors.add(new VampireProofExecutor("vampire_lrs+1011", smt, latch, "lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:sos=theory:sp=occurrence:urr=ec_only:updr=off_" + (TIMEOUT_S * 10)));
//            executors.add(new VampireProofExecutor("vampire_lrs+11_20", smt, latch, "lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_" + (TIMEOUT_S * 10)));
//            executors.add(new VampireProofExecutor("vampire_lrs+1_7", smt, latch, "lrs+1_7_av=off:cond=fast:fde=none:gs=on:gsem=off:lcm=predicate:nm=6:nwc=1:stl=30:sd=3:ss=axioms:sos=on:sp=occurrence:updr=off_" + (TIMEOUT_S * 10)));

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
        System.out.println("\t\t| Solve:\t" + (System.nanoTime() - startNs) / 1000000);
        checker.printFormula(smt, "rr_unsat_core");

        if (smallestRRCore == null) {
            return Optional.empty();
        }

        printMessage("Winner:\t" + winner);
        printStylizedMessage(smallestRRCore::toString, ANSI_RED + ANSI_BLUE_BACKGROUND);
        printStylizedMessage(preambleCore::toString, ANSI_RED + ANSI_BLUE_BACKGROUND);

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

        long startMs = System.currentTimeMillis();
        MyZ3Context context = schema.getContext();
        context.pushTrackConsts();
        try {
            CountingBoundEstimator cbe = new CountingBoundEstimator();
            UnsatCoreBoundEstimator boundEstimator = new UnsatCoreBoundEstimator(cbe);
            Map<String, Integer> bounds = boundEstimator.calculateBounds(schema, subTrace);

            Map<String, Integer> slackBounds = Maps.transformValues(bounds, n -> n + boundSlack);
            BoundedDeterminacyFormula baseFormula = new BoundedDeterminacyFormula(schema, views, slackBounds,
                    true, TextOption.NO_TEXT, null, preambleCore);
            this.formulaBuilder = new UnsatCoreFormulaBuilder(baseFormula, policies);
            System.out.println("\t\t| Bounded RRL core 1:\t" + (System.currentTimeMillis() - startMs));

            UnsatCoreFormulaBuilder.Formulas<ReturnedRowLabel> fs = formulaBuilder.buildReturnedRowsOnly(subTrace);
            solver = context.mkSolver(context.mkSymbol("QF_UF"));

            if (subTrace.size() == 1) { // Only the current query is in the trace.  It doesn't depend on any previous!
                // However, only return after making a solver, which is expected by subsequent callers to `getSolver()`.
                return Collections.emptySet();
            }

            solver.push();
            solver.add(fs.getBackground().toArray(new BoolExpr[0]));
            System.out.println("\t\t| Bounded RRL core 2:\t" + (System.currentTimeMillis() - startMs));
            try (UnsatCoreEnumerator<ReturnedRowLabel> uce
                         = new UnsatCoreEnumerator<>(context, solver, fs.getLabeledExprs(), Order.ARBITRARY)) {
                System.out.println("\t\t| Bounded RRL core 3:\t" + (System.currentTimeMillis() - startMs));
                Set<ReturnedRowLabel> s = uce.getStartingUnsatCore();
                System.out.println("\t\t| Bounded RRL core 4:\t" + (System.currentTimeMillis() - startMs));
                s = s.stream().map(l -> (ReturnedRowLabel) DecisionTemplateGenerator.backMapLabel(l, subTrace)).collect(Collectors.toSet());
                return s;
            } finally {
                solver.pop();
            }
        } finally {
            context.popTrackConsts();
            System.out.println("\t\t| Bounded RRL core:\t" + (System.currentTimeMillis() - startMs));
        }
    }

    // MUST be called only after `minimizeRRCore`.
    public UnsatCoreFormulaBuilder getFormulaBuilder() {
        return Objects.requireNonNull(formulaBuilder);
    }

    // MUST be called only after `minimizeRRCore`.
    public Solver getSolver() {
        return Objects.requireNonNull(solver);
    }
}
