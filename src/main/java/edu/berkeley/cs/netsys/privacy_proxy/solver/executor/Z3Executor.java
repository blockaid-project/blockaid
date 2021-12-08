package edu.berkeley.cs.netsys.privacy_proxy.solver.executor;

import com.google.common.collect.ImmutableList;

import java.util.concurrent.CountDownLatch;
import java.util.function.Consumer;

public class Z3Executor extends ProcessSMTExecutor {
    private static final ImmutableList<String> command = ImmutableList.of("z3", "-smt2", "/dev/stdin");

    // unsat core
    public Z3Executor(String name, String solver, CountDownLatch latch) {
        super(name, solver, latch, command, false, true, false, true);
    }

    public Z3Executor(String name, String solver, Consumer<String> signalFunc) {
        super(name, solver, signalFunc, command, false, true, false, true);
    }

    public Z3Executor(String name, String solver, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive) {
        super(name, solver, latch, command, satConclusive, unsatConclusive, unknownConclusive, false);
    }

    public Z3Executor(String name, String solver, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive, boolean unsatCore) {
        super(name, solver, latch, command, satConclusive, unsatConclusive, unknownConclusive, unsatCore);
    }
}
