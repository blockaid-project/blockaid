package solver.executor;

import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import solver.executor.SMTExecutor;

import java.util.concurrent.CountDownLatch;

public class Z3ExecutorDirect extends SMTExecutor {
    private Solver solver;
    private CountDownLatch latch;
    private boolean satConclusive;
    private boolean unsatConclusive;
    private Status result = Status.UNKNOWN;
    private Thread thisThread = null;

    public Z3ExecutorDirect(Solver solver, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive) {
        super(solver.toString(), latch, new String[]{}, satConclusive, unsatConclusive);
        this.solver = solver;
        this.latch = latch;
        this.satConclusive = satConclusive;
        this.unsatConclusive = unsatConclusive;
    }

    @Override
    public void run() {
        thisThread = Thread.currentThread();
        result = solver.check();
        if ((this.result == Status.UNSATISFIABLE && unsatConclusive) || (this.result == Status.SATISFIABLE && satConclusive)) {
            this.latch.countDown();
        } else {
            result = Status.UNKNOWN;
        }
        while (true);
    }

    public synchronized void signalShutdown() {
//        if (thisThread != null && thisThread.isAlive()) {
//            thisThread.interrupt();
//        }
    }

    public Status getResult() {
        return result;
    }
}
