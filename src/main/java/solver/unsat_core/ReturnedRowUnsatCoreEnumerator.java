package solver.unsat_core;

import solver.DecisionTemplateGenerator;
import solver.RRLVampireDeterminacyFormula;
import solver.labels.ReturnedRowLabel;
import cache.trace.*;
import com.google.common.collect.*;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import policy_checker.Policy;
import policy_checker.QueryChecker;
import solver.*;
import solver.executor.ProcessSMTExecutor;
import solver.executor.SMTExecutor;
import solver.executor.VampireProofExecutor;

import java.util.*;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static util.TerminalColor.*;

public class ReturnedRowUnsatCoreEnumerator {
    private static final int TIMEOUT_S = 20;

    private final QueryChecker checker;
    private final Schema schema;
    private final Collection<Policy> policies;
    private final Collection<Query> views;
    private final RRLVampireDeterminacyFormula myFormula;

    private UnsatCoreFormulaBuilder formulaBuilder = null;

    public ReturnedRowUnsatCoreEnumerator(QueryChecker checker, Schema schema, Collection<Policy> policies,
                                          Collection<Query> views) {
        this.checker = checker;
        this.schema = schema;
        this.policies = policies;
        this.views = views;
        this.myFormula = new RRLVampireDeterminacyFormula(schema, views);
    }

    // Returns empty if formula is not determined UNSAT.
    public Optional<Set<ReturnedRowLabel>> getOne(UnmodifiableLinearQueryTrace trace) {
        boolean shrank = false;
        int maxBound = Collections.max(new CountingBoundEstimator().calculateBounds(schema, trace).values());
        if (maxBound > 0) {
            long startMs = System.currentTimeMillis();
            String smtVampire = myFormula.generateSMT(trace);
            System.out.println("\t\t| Prepare Vampire:\t" + (System.currentTimeMillis() - startMs));

            ArrayList<ProcessSMTExecutor> executors = new ArrayList<>();
            CountDownLatch latch = new CountDownLatch(1);
            executors.add(new VampireProofExecutor("vampire_lrs+10_1", smtVampire, latch, "lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_" + (TIMEOUT_S * 10)));
            executors.add(new VampireProofExecutor("vampire_dis+11_3", smtVampire, latch, "dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_" + (TIMEOUT_S * 10)));
            executors.add(new VampireProofExecutor("vampire_dis+3_1", smtVampire, latch, "dis+3_1_cond=on:fde=unused:nwc=1:sd=1:ss=axioms:st=1.2:sos=on:sac=on:add=off:afp=40000:afq=1.4:anc=none_" + (TIMEOUT_S * 10)));
            executors.add(new VampireProofExecutor("vampire_dis+2_3", smtVampire, latch, "dis+2_3_av=off:cond=on:fsr=off:lcm=reverse:lma=on:nwc=1:sos=on:sp=reverse_arity_" + (TIMEOUT_S * 10)));
//            executors.add(new VampireProofExecutor("vampire_lrs+1011", smtVampire, latch, "lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:sos=theory:sp=occurrence:urr=ec_only:updr=off_" + (TIMEOUT_S * 10)));
//            executors.add(new VampireProofExecutor("vampire_lrs+11_20", smtVampire, latch, "lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_" + (TIMEOUT_S * 10)));
//            executors.add(new VampireProofExecutor("vampire_lrs+1_7", smtVampire, latch, "lrs+1_7_av=off:cond=fast:fde=none:gs=on:gsem=off:lcm=predicate:nm=6:nwc=1:stl=30:sd=3:ss=axioms:sos=on:sp=occurrence:updr=off_" + (TIMEOUT_S * 10)));

            for (SMTExecutor executor : executors) {
                executor.start();
            }

            startMs = System.currentTimeMillis();
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

            Set<ReturnedRowLabel> smallestCore = null;
            for (ProcessSMTExecutor e : executors) {
                if (e.getResult() != Status.UNSATISFIABLE) {
                    continue;
                }
                System.out.println(e.getName());
                Set<ReturnedRowLabel> core = Pattern.compile("ReturnedRowLabel!(\\d+)!(\\d+)").matcher(e.getOutput())
                        .results()
                        .map(r -> new ReturnedRowLabel(Integer.parseInt(r.group(1)), Integer.parseInt(r.group(2))))
                        .collect(Collectors.toSet());
                System.out.println(ANSI_RED + ANSI_BLUE_BACKGROUND + core + ANSI_RESET);
                if (smallestCore == null || smallestCore.size() > core.size()) {
                    smallestCore = core;
                }
            }
            System.out.println("\t\t| Vampire:\t" + (System.currentTimeMillis() - startMs));
            checker.printFormula(smtVampire, "rr_unsat_core");

            if (smallestCore == null) {
                return Optional.empty();
            }
            trace = trace.getSubTrace(
                    smallestCore.stream()
                            .map(rrl -> new QueryTupleIdxPair(rrl.getQueryIdx(), rrl.getRowIdx()))
                            .collect(ImmutableList.toImmutableList())
            );
            shrank = true;
        }

        long startMs = System.currentTimeMillis();
        MyZ3Context context = schema.getContext();
        context.startTrackingConsts();
        try {
            Solver solver = context.mkSolver();

            CountingBoundEstimator cbe = new CountingBoundEstimator();
            BoundEstimator boundEstimator = new UnsatCoreBoundEstimator(cbe);
            Map<String, Integer> bounds = boundEstimator.calculateBounds(schema, trace);
            Map<String, Integer> slackBounds = Maps.transformValues(bounds, n -> n + 1);
            BoundedDeterminacyFormula baseFormula = new BoundedDeterminacyFormula(schema, views, slackBounds,
                    true, DeterminacyFormula.TextOption.NO_TEXT, null);
            this.formulaBuilder = new UnsatCoreFormulaBuilder(baseFormula, policies);
            System.out.println("\t\t| Bounded RRL core 1:\t" + (System.currentTimeMillis() - startMs));

            if (trace.size() == 1) { // Only the current query is in the trace.  It doesn't depend on any previous!
                return Optional.of(Collections.emptySet());
            }

            UnsatCoreFormulaBuilder.Formulas<ReturnedRowLabel> fs = formulaBuilder.buildReturnedRowsOnly(trace);
            solver.add(fs.getBackground().toArray(new BoolExpr[0]));
            System.out.println("\t\t| Bounded RRL core 2:\t" + (System.currentTimeMillis() - startMs));
            UnsatCoreEnumerator<ReturnedRowLabel> uce = new UnsatCoreEnumerator<>(context, solver, fs.getLabeledExprs(),
                    Order.ARBITRARY);
            System.out.println("\t\t| Bounded RRL core 3:\t" + (System.currentTimeMillis() - startMs));
            Set<ReturnedRowLabel> s = uce.getStartingUnsatCore();
            System.out.println("\t\t| Bounded RRL core 4:\t" + (System.currentTimeMillis() - startMs));
            if (shrank) {
                SubQueryTrace sqt = (SubQueryTrace) trace;
                s = s.stream().map(l -> (ReturnedRowLabel) DecisionTemplateGenerator.backMapLabel(l, sqt)).collect(Collectors.toSet());
            }
            return Optional.of(s);
        } finally {
            context.stopTrackingConsts();
            System.out.println("\t\t| Bounded RRL core:\t" + (System.currentTimeMillis() - startMs));
        }
    }

    public UnsatCoreFormulaBuilder getFormulaBuilder() {
        return formulaBuilder;
    }
}
