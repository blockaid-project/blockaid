package edu.berkeley.cs.netsys.privacy_proxy.solver.executor;

import com.google.common.collect.ImmutableList;

import java.util.concurrent.CountDownLatch;
import java.util.function.Consumer;

public class CVCExecutor extends ProcessSMTExecutor {
    private static ImmutableList<String> makeCommand(String binary) {
        return ImmutableList.of(
                // for some reason calling cvc4 directly results in broken pipes for stdin..
                "term_to_kill", binary, "--lang", "smtlib2", "--quiet"
        );
    }

    // unsat core
    public CVCExecutor(String binary, String name, String smt, CountDownLatch latch) {
        this(binary, name, smt, latch, false, true, false, true);
    }

    public CVCExecutor(String binary, String name, String smt, Consumer<String> signalFunc) {
        this(binary, name, smt, signalFunc, false, true, false, true);
    }

    public CVCExecutor(String binary, String name, String smt, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive) {
        this(binary, name, smt, latch, satConclusive, unsatConclusive, unknownConclusive, false);
    }

    public CVCExecutor(String binary, String name, String smt, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive, boolean runCore) {
        super(name, smt, latch, makeCommand(binary), satConclusive, unsatConclusive, unknownConclusive, runCore);
    }

    public CVCExecutor(String binary, String name, String smt, Consumer<String> signalFunc, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive, boolean runCore) {
        super(name, smt, signalFunc, makeCommand(binary), satConclusive, unsatConclusive, unknownConclusive, runCore);
    }
}
