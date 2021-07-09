package solver.executor;

import cache.QueryTrace;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import solver.DeterminacyFormula;
import solver.MyZ3Context;

import java.util.concurrent.CountDownLatch;

public class Z3ExecutorDirect extends SMTExecutor {
    private final MyZ3Context context;
    private final DeterminacyFormula formula;
    private final QueryTrace queries;
    private Solver solver = null;
    private boolean shuttingDown = false;

    public Z3ExecutorDirect(String name, MyZ3Context context, DeterminacyFormula formula, QueryTrace queries, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive) {
        super(name, latch, satConclusive, unsatConclusive, unknownConclusive, false);
        this.context = context;
        this.formula = formula;
        this.queries = queries;
    }

    @Override
    protected Status doRunNormal() throws InterruptedException {
        synchronized (this) {
            if (shuttingDown) {
                return Status.UNKNOWN;
            }
            solver = context.mkSolver();
            for (BoolExpr expr : formula.makeFormula(queries)) {
                solver.add(expr);
            }
        }
        // todo: fix race condition
        return solver.check();
    }

    @Override
    protected Status doRunUnsatCore() throws InterruptedException {
        throw new UnsupportedOperationException();
    }

    public synchronized void signalShutdown() {
        if (solver != null) {
            solver.interrupt();
        }
        shuttingDown =  true;
    }
}
