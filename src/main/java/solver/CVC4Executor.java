package solver;

import com.microsoft.z3.Solver;

import java.util.concurrent.CountDownLatch;

public class CVC4Executor extends SMTExecutor {
    private static String[] command = new String[]{
            "term_to_kill",
            "cvc4",
            "--lang", "smtlib2",
//            "--finite-model-find",
            "-q", "-"
    };

    // unsat core
    public CVC4Executor(String solver, CountDownLatch latch) {
        super(solver, latch, command);
    }

    public CVC4Executor(String solver, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive) {
        super(solver, latch, command, satConclusive, unsatConclusive);
    }
}
