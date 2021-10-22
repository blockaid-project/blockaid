package edu.berkeley.cs.netsys.privacy_proxy.solver.executor;

import java.util.concurrent.CountDownLatch;

public class CVC4Executor extends ProcessSMTExecutor {
    private static final String[] command = new String[]{
            // for some reason calling cvc4 directly results in broken pipes for stdin..
//            "term_to_kill",
//            "sh", "-c", "cat /dev/stdin | cvc4 --lang smtlib2 -q -",
            "term_to_kill", "cvc4", "--lang", "smtlib2", "--quiet"
    };

    // unsat core
    public CVC4Executor(String name, String smt, CountDownLatch latch) {
        super(name, smt, latch, command, false, true, false, true);
    }

    public CVC4Executor(String name, String smt, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive) {
        super(name, smt, latch, command, satConclusive, unsatConclusive, unknownConclusive, false);
    }

    public CVC4Executor(String name, String smt, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive, boolean runCore) {
        super(name, smt, latch, command, satConclusive, unsatConclusive, unknownConclusive, runCore);
    }
}
