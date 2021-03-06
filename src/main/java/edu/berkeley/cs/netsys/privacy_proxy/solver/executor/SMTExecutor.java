package edu.berkeley.cs.netsys.privacy_proxy.solver.executor;

import com.microsoft.z3.Status;

import java.util.concurrent.CountDownLatch;
import java.util.function.Consumer;

public abstract class SMTExecutor extends Thread {
    private final Consumer<String> signalFunc;
    private final boolean satConclusive;
    private final boolean unsatConclusive;
    private final boolean unknownConclusive;
    private final boolean runCore;

    private Status result = null;
    private String[] core = null;

    protected SMTExecutor(String name, Consumer<String> signalFunc, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive, boolean runCore) {
        this.signalFunc = signalFunc;
        this.satConclusive = satConclusive;
        this.unsatConclusive = unsatConclusive;
        this.unknownConclusive = unknownConclusive;
        this.runCore = runCore;
        setName(name);
    }

    protected SMTExecutor(String name, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive, boolean runCore) {
        this(name, s -> latch.countDown(), satConclusive, unsatConclusive, unknownConclusive, runCore);
    }

    @Override
    public void run() {
        try {
            if (this.runCore) {
                result = doRunUnsatCore();
            } else {
                result = doRunNormal();
            }
            if ((this.result == Status.UNSATISFIABLE && unsatConclusive) || (this.result == Status.SATISFIABLE && satConclusive) || (this.result == Status.UNKNOWN && unknownConclusive)) {
                this.signalFunc.accept(getName());
            } else {
                result = Status.UNKNOWN;
            }
        } catch (InterruptedException e) {
            result = Status.UNKNOWN;
        }
    }

    protected abstract Status doRunNormal() throws InterruptedException;

    protected abstract Status doRunUnsatCore() throws InterruptedException;

    protected void setUnsatCore(String[] core) {
        this.core = core;
        if (this.core.length == 1 && this.core[0].equals("")) {
            this.core = new String[0];
        }
    }

    public abstract void signalShutdown();

    public Status getResult() {
        return result;
    }

    public String[] getUnsatCore() {
        return core;
    }
}
