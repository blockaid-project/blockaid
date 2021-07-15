package solver.executor;

import cache.QueryTrace;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import solver.*;

import java.util.Collection;
import java.util.Map;
import java.util.concurrent.CountDownLatch;

public class BoundedExecutor extends SMTExecutor {
    private final Schema schema;
    private final Collection<Query> views;
    private final QueryTrace queries;
    private Solver solver;
    private boolean shuttingDown = false;

    public BoundedExecutor(String name, CountDownLatch latch, Schema schema, Collection<Query> views, QueryTrace queries) {
        super(name, latch, true, false, false, false);
        this.schema = schema;
        this.views = views;
        this.queries = queries;
    }

    @Override
    protected Status doRunNormal() {
        long startTime = System.currentTimeMillis();

        MyZ3Context context = schema.getContext();
        // this sucks - this executor cannot exit even if we get a fast unsat, until formula generation is done
        BoundEstimator boundEstimator = new UnsatCoreBoundEstimator(new FixedBoundEstimator(0));
        Map<String, Integer> bounds = boundEstimator.calculateBounds(schema, queries);
        DeterminacyFormula boundedDeterminacyFormula = new BoundedDeterminacyFormula(schema, views, bounds, true);

        synchronized (this) {
            if (shuttingDown) {
                return Status.UNKNOWN;
            }
            solver = context.mkSolver();
            for (BoolExpr expr : boundedDeterminacyFormula.makeFormula(queries)) {
                solver.add(expr);
            }
        }

        System.out.println("\t| Make bounded:\t" + (System.currentTimeMillis() - startTime));

        // todo: fix race condition
        return solver.check();
    }

    @Override
    protected Status doRunUnsatCore() {
        throw new UnsupportedOperationException();
    }

    @Override
    public synchronized void signalShutdown() {
        if (solver != null) {
            solver.interrupt();
        }
        shuttingDown = true;
    }
}
