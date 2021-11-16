package edu.berkeley.cs.netsys.privacy_proxy.solver.executor;

import com.google.common.collect.ImmutableList;

import java.util.concurrent.CountDownLatch;

public class CVCExecutor extends ProcessSMTExecutor {
    // unsat core
    public CVCExecutor(String binary, String name, String smt, CountDownLatch latch) {
        this(binary, name, smt, latch, false, true, false, true);
    }

    public CVCExecutor(String binary, String name, String smt, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive) {
        this(binary, name, smt, latch, satConclusive, unsatConclusive, unknownConclusive, false);
    }

    public CVCExecutor(String binary, String name, String smt, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive, boolean runCore) {
        super(name, smt, latch, ImmutableList.of(
                // for some reason calling cvc4 directly results in broken pipes for stdin..
                "term_to_kill", binary, "--lang", "smtlib2", "--quiet"
        ), satConclusive, unsatConclusive, unknownConclusive, runCore);
    }
}
