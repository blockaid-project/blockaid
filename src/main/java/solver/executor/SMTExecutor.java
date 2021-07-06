package solver.executor;

import com.microsoft.z3.Status;

import java.util.concurrent.CountDownLatch;

public abstract class SMTExecutor extends Thread {
    private final CountDownLatch latch;
    private final boolean satConclusive;
    private final boolean unsatConclusive;
    private final boolean unknownConclusive;
    private final boolean runCore;

    private Status result = null;
    private String[] core = null;

    protected SMTExecutor(String name, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive, boolean runCore) {
        this.latch = latch;
        this.satConclusive = satConclusive;
        this.unsatConclusive = unsatConclusive;
        this.unknownConclusive = unknownConclusive;
        this.runCore = runCore;
        setName(name);
    }

    public void run() {
        if (this.runCore) {
            this.runUnsatCore();
        } else {
            this.runNormal();
        }
    }

    protected abstract Status doRunNormal() throws InterruptedException;

    private void runNormal() {
        try {
            result = doRunNormal();
            if ((this.result == Status.UNSATISFIABLE && unsatConclusive) || (this.result == Status.SATISFIABLE && satConclusive) || (this.result == Status.UNKNOWN && unknownConclusive)) {
                this.latch.countDown();
            } else {
                result = Status.UNKNOWN;
            }
        } catch (InterruptedException e) {
            result = Status.UNKNOWN;
        }
    }

    protected abstract Status doRunUnsatCore() throws InterruptedException;

    protected void setUnsatCore(String[] core) {
        this.core = core;
    }

    private void runUnsatCore() {
        try {
            result = doRunUnsatCore();
            if (this.result == Status.UNSATISFIABLE) {
                this.latch.countDown();
            } else {
                result = Status.UNKNOWN;
            }
        } catch (InterruptedException e) {
            result = Status.UNKNOWN;
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
