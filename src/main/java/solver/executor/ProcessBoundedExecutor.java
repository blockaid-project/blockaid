package solver.executor;

import cache.QueryTrace;
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
        // this sucks - this executor cannot exit even if we get a fast unsat, until initial bound estimation is done
         BoundEstimator boundEstimator = new UnsatCoreBoundEstimator(new FixedBoundEstimator(0));
//        BoundEstimator boundEstimator = new FixedBoundEstimator(0);
        Map<String, Integer> bounds = boundEstimator.calculateBounds(schema, queries);

        while (!shuttingDown) {
            System.err.println(bounds);
            DeterminacyFormula boundedDeterminacyFormula = new BoundedDeterminacyFormula(schema, views, bounds, true);
            String smt = boundedDeterminacyFormula.generateSMT(queries);

            CountDownLatch latch = new CountDownLatch(1);
            long startTime;
            synchronized (this) {
                if (shuttingDown) {
                    return Status.UNKNOWN;
                }
                 executor = new Z3Executor("z3_bounded_runner", smt, latch, true, true, true, true);
//                executor = new CVC4Executor("cvc4_bounded_runner", smt, latch, true, true, true, true);
                startTime = System.nanoTime();
                executor.start();
            }

            latch.await();
            System.err.println("bounded solve time: " + (System.nanoTime() - startTime) / 1e9);

            if (executor.getResult() == Status.SATISFIABLE) {
                return Status.SATISFIABLE;
            } else if (executor.getResult() == Status.UNSATISFIABLE && executor.getUnsatCore().length > 0) {
                for (String relation : executor.getUnsatCore()) {
                    bounds.computeIfPresent(relation, (k, v) -> v + 1);
                }
            } else {
                // UNKNOWN - just increment everything
                for (String relation : bounds.keySet()) {
                    bounds.computeIfPresent(relation, (k, v) -> v + 1);
                }
            }
        }

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
