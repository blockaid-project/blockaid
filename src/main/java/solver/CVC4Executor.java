package solver;

import com.microsoft.z3.Solver;

import java.util.concurrent.CountDownLatch;

public class CVC4Executor extends SMTExecutor {
    private static String[] command = new String[]{
            // for some reason calling cvc4 directly results in broken pipes for stdin..
//            "term_to_kill",
//            "sh", "-c", "cat /dev/stdin | cvc4 --lang smtlib2 -q -",
            "cvc4", "--lang", "smtlib2", "--quiet"
    };

    // unsat core
    public CVC4Executor(String solver, CountDownLatch latch) {
        super(solver, latch, command);
    }

    public CVC4Executor(String solver, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive) {
        super(solver, latch, command, satConclusive, unsatConclusive);
    }
}
