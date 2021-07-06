package solver.executor;

import java.util.concurrent.CountDownLatch;

public class Z3Executor extends ProcessSMTExecutor {
    private static String[] command = new String[]{
            "z3",
            "-smt2",
            "/dev/stdin",
    };

    // unsat core
    public Z3Executor(String name, String solver, CountDownLatch latch) {
        super(name, solver, latch, command, false, true, false);
    }

    public Z3Executor(String name, String solver, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive) {
        super(name, solver, latch, command, satConclusive, unsatConclusive, unknownConclusive);
    }
}
