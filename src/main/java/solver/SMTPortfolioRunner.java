package solver;

import com.microsoft.z3.Status;
import policy_checker.QueryChecker;
import solver.executor.CVC4Executor;
import solver.executor.SMTExecutor;
import solver.executor.VampireExecutor;
import solver.executor.Z3Executor;
import util.Logger;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import static util.Logger.printMessage;
import static util.TerminalColor.ANSI_RED_BACKGROUND;

public class SMTPortfolioRunner {
    private final QueryChecker checker;
    private final long timeout_ms;

    public SMTPortfolioRunner(QueryChecker checker, long timeout_ms) {
        this.checker = checker;
        this.timeout_ms = timeout_ms;
    }

    // Returns the winner.
    public Optional<SMTExecutor> runExecutors(List<SMTExecutor> executors, CountDownLatch latch) {
        for (SMTExecutor executor : executors) {
            executor.start();
        }

        try {
            latch.await(timeout_ms, TimeUnit.MILLISECONDS);
            for (SMTExecutor executor : executors) {
                executor.signalShutdown();
            }
            for (SMTExecutor executor : executors) {
                executor.join();
            }
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }

        for (SMTExecutor executor : executors) {
            if (executor.getResult() != Status.UNKNOWN) {
                return Optional.of(executor);
            }
        }

        return Optional.empty();
    }

    // Returns true if compliant, false if not / unknown.
    public boolean checkFastUnsatFormula(String formula, String fileNamePrefix) {
        CountDownLatch latch = new CountDownLatch(1);
        ArrayList<SMTExecutor> executors = new ArrayList<>();
        executors.add(new Z3Executor("z3_fast", formula, latch, false, true, false));
        executors.add(new CVC4Executor("cvc4_fast", formula, latch, false, true, false));
        executors.add(new VampireExecutor("vampire_lrs+10_1_fast", "lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_10000", formula, latch, false, true, false));
        executors.add(new VampireExecutor("vampire_lrs+1_3_fast", "lrs+1_3:2_afr=on:afp=100000:afq=1.0:anc=all_dependent:cond=on:fde=none:gs=on:inw=on:ile=on:irw=on:nm=6:nwc=1:stl=30:sos=theory:updr=off:uhcvi=on_10000", formula, latch, false, true, false));
        executors.add(new VampireExecutor("vampire_dis+11_3_fast", "dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_10000", formula, latch, false, true, false));
        executors.add(new VampireExecutor("vampire_dis+3_1_fast", "dis+3_1_cond=on:fde=unused:nwc=1:sd=1:ss=axioms:st=1.2:sos=on:sac=on:add=off:afp=40000:afq=1.4:anc=none_10000", formula, latch, false, true, false));
        executors.add(new VampireExecutor("vampire_dis+2_3_fast", "dis+2_3_av=off:cond=on:fsr=off:lcm=reverse:lma=on:nwc=1:sos=on:sp=reverse_arity_10000", formula, latch, false, true, false));
//        executors.add(new VampireExecutor("vampire_lrs+1011_fast", "lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:sos=theory:sp=occurrence:urr=ec_only:updr=off_10000", formula, latch, false, true, false));
//        executors.add(new VampireExecutor("vampire_lrs+11_20_fast", "lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_10000", formula, latch, false, true, false));
//        executors.add(new VampireExecutor("vampire_lrs+1_7_fast", "lrs+1_7_av=off:cond=fast:fde=none:gs=on:gsem=off:lcm=predicate:nm=6:nwc=1:stl=30:sd=3:ss=axioms:sos=on:sp=occurrence:updr=off_10000", formula, latch, false, true, false));
        checker.printFormula(formula, fileNamePrefix);

        long startNs = System.nanoTime();
        Optional<SMTExecutor> oWinner = runExecutors(executors, latch);
        final long solverDurationNs = System.nanoTime() - startNs;

        if (oWinner.isPresent()) {
            SMTExecutor winner = oWinner.get();
            printMessage("\t| Invoke solvers:\t" + solverDurationNs / 1000000 + "," + winner.getName());
            return winner.getResult() == Status.UNSATISFIABLE;
        }

        // all timeout/inconclusive
        Logger.printStylizedMessage("All solvers time out / inconclusive", ANSI_RED_BACKGROUND);
        return false;
    }
}
