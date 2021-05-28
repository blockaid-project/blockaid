package solver.executor;

import solver.executor.SMTExecutor;

import java.util.concurrent.CountDownLatch;

public class Z3Executor extends SMTExecutor {
    private static String[] command = new String[]{
            "z3",
            "-smt2",
            "/dev/stdin",
    };

    // unsat core
    public Z3Executor(String solver, CountDownLatch latch) {
        super(solver, latch, command);
    }

    public Z3Executor(String solver, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, String name) {
        super(solver, latch, command, satConclusive, unsatConclusive, name);
    }
}
