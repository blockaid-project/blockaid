package solver;

import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import java.io.BufferedWriter;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.Scanner;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicBoolean;

public class Z3ExecutorDirect extends SMTExecutor {
    private Solver solver;
    private CountDownLatch latch;
    private boolean satConclusive;
    private boolean unsatConclusive;
    private Status result = null;
    private Process process = null;
    private AtomicBoolean shuttingDown = new AtomicBoolean(false);

    public Z3ExecutorDirect(Solver solver, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive) {
        super(solver.toString(), latch, new String[]{}, satConclusive, unsatConclusive);
        this.solver = solver;
        this.latch = latch;
        this.satConclusive = satConclusive;
        this.unsatConclusive = unsatConclusive;
    }

    @Override
    public void run() {
        result = solver.check();
        if ((this.result == Status.UNSATISFIABLE && unsatConclusive) || (this.result == Status.SATISFIABLE && satConclusive)) {
            this.latch.countDown();
        } else {
            result = Status.UNKNOWN;
        }
    }

    public synchronized void signalShutdown() {

    }

    public Status getResult() {
        return result;
    }
}
