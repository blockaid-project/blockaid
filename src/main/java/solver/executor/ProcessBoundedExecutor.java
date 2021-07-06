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

public class ProcessBoundedExecutor extends SMTExecutor {
    private final Schema schema;
    private final Collection<Query> views;
    private final QueryTrace queries;
    private ProcessSMTExecutor executor = null;
    private boolean shuttingDown = false;

    public ProcessBoundedExecutor(String name, CountDownLatch latch, Schema schema, Collection<Query> views, QueryTrace queries) {
        super(name, latch, true, false, false, false);
        this.schema = schema;
        this.views = views;
        this.queries = queries;
    }

    @Override
    protected Status doRunNormal() throws InterruptedException {
        long startTime = System.currentTimeMillis();

        // this sucks - this executor cannot exit even if we get a fast unsat, until formula generation is done
        BoundEstimator boundEstimator = new UnsatCoreBoundEstimator(new FixedBoundEstimator(0));
        Map<String, Integer> bounds = boundEstimator.calculateBounds(schema, queries);
        DeterminacyFormula boundedDeterminacyFormula = new BoundedDeterminacyFormula(schema, views, bounds);

        CountDownLatch latch = new CountDownLatch(1);
        synchronized (this) {
            if (shuttingDown) {
                return Status.UNKNOWN;
            }
            executor = new Z3Executor("z3_bounded_runner", boundedDeterminacyFormula.generateSMT(queries), latch, true, true, true);

            System.out.println("\t| Make bounded:\t" + (System.currentTimeMillis() - startTime));
            executor.start();
        }

        latch.await();

        return executor.getResult();
    }

    @Override
    protected Status doRunUnsatCore() throws InterruptedException {
        throw new UnsupportedOperationException();
    }

    @Override
    public synchronized void signalShutdown() {
        if (executor != null) {
            executor.signalShutdown();
        }
        shuttingDown = true;
    }
}
