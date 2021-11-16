package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.Status;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.QueryChecker;
import edu.berkeley.cs.netsys.privacy_proxy.solver.executor.*;
import edu.berkeley.cs.netsys.privacy_proxy.util.Logger;
import edu.berkeley.cs.netsys.privacy_proxy.util.VampireConfigurations;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import static edu.berkeley.cs.netsys.privacy_proxy.util.Logger.printMessage;
import static edu.berkeley.cs.netsys.privacy_proxy.util.TerminalColor.ANSI_RED_BACKGROUND;

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
        checker.printFormula(formula, fileNamePrefix);

        CountDownLatch latch = new CountDownLatch(1);
        ArrayList<SMTExecutor> executors = new ArrayList<>();
        executors.add(new Z3Executor("z3_fast", formula, latch, false, true, false));
//        executors.add(new CVCExecutor("cvc4", "cvc4_fast", formula, latch, false, true, false));
        executors.add(new CVCExecutor("cvc5", "cvc5_fast", formula, latch, false, true, false));
        for (Map.Entry<String, String> entry : VampireConfigurations.getAll(timeout_ms * 1000 * 10).entrySet()) {
            String configName = entry.getKey(), configString = entry.getValue();
            executors.add(new VampireExecutor(configName + "_fast", configString, formula, latch, false, true, false));
        }

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
