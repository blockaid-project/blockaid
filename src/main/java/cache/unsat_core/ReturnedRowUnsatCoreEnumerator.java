package cache.unsat_core;

import cache.BoundedUnsatCoreDeterminacyFormula;
import cache.DecisionTemplateGenerator;
import cache.MyUnsatCoreDeterminacyFormula;
import cache.labels.Label;
import cache.labels.ReturnedRowLabel;
import cache.trace.*;
import com.google.common.collect.*;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import policy_checker.Policy;
import policy_checker.QueryChecker;
import solver.*;
import solver.executor.CVC4Executor;
import solver.executor.ProcessSMTExecutor;
import solver.executor.SMTExecutor;
import solver.executor.VampireProofExecutor;

import java.util.*;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static util.TerminalColor.*;

public class ReturnedRowUnsatCoreEnumerator {
    private static final int TIMEOUT_S = 20;

    private final QueryChecker checker;
    private final Schema schema;
    private final Collection<Policy> policies;
    private final Collection<Query> views;
    private final MyUnsatCoreDeterminacyFormula myFormula;

    public ReturnedRowUnsatCoreEnumerator(QueryChecker checker, Schema schema, Collection<Policy> policies,
                                          Collection<Query> views) {
        this.checker = checker;
        this.schema = schema;
        this.policies = policies;
        this.views = views;
        this.myFormula = new MyUnsatCoreDeterminacyFormula(schema, views);
    }

    // Returns empty if formula is not determined UNSAT.
    public Optional<Set<ReturnedRowLabel>> getOne(UnmodifiableLinearQueryTrace trace) {
        UnmodifiableLinearQueryTrace traceToUse = trace;
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
            traceToUse = trace.getSubTrace(
                    smallestCore.stream()
                            .map(rrl -> new QueryTupleIdxPair(rrl.getQueryIdx(), rrl.getRowIdx()))
                            .collect(ImmutableList.toImmutableList())
            );
            shrank = true;
        }

        if (traceToUse.size() == 1) {
            return Optional.of(Collections.emptySet());
        }

        long startMs = System.currentTimeMillis();
        MyZ3Context context = schema.getContext();
        context.startTrackingConsts();
        Solver solver = context.mkSolver();
        BoundedUnsatCoreDeterminacyFormula formula = BoundedUnsatCoreDeterminacyFormula.create(schema, policies,
                views, traceToUse, BoundedUnsatCoreDeterminacyFormula.LabelOption.RETURNED_ROWS_ONLY);
        System.out.println("\t\t| Bounded RRL core 1:\t" + (System.currentTimeMillis() - startMs));
        solver.add(Iterables.toArray(formula.makeBackgroundFormulas(), BoolExpr.class));
        Map<ReturnedRowLabel, BoolExpr> labeledExprs = formula.makeLabeledExprs().entrySet().stream()
                .collect(Collectors.toMap(e -> (ReturnedRowLabel) e.getKey(), Map.Entry::getValue));
        System.out.println("\t\t| Bounded RRL core 2:\t" + (System.currentTimeMillis() - startMs));
        UnsatCoreEnumerator<ReturnedRowLabel> uce = new UnsatCoreEnumerator<>(context, solver, labeledExprs, Order.ARBITRARY);
        System.out.println("\t\t| Bounded RRL core 3:\t" + (System.currentTimeMillis() - startMs));
        Set<ReturnedRowLabel> s = uce.next().get();
        System.out.println("\t\t| Bounded RRL core 4:\t" + (System.currentTimeMillis() - startMs));
        if (shrank) {
            SubQueryTrace sqt = (SubQueryTrace) traceToUse;
            s = s.stream().map(l -> (ReturnedRowLabel) DecisionTemplateGenerator.backMapLabel(l, sqt)).collect(Collectors.toSet());
        }
        System.out.println("\t\t| Bounded RRL core:\t" + (System.currentTimeMillis() - startMs));
        context.stopTrackingConsts();
        return Optional.of(s);
    }
}
