package edu.berkeley.cs.netsys.privacy_proxy.solver.executor;

import com.google.common.collect.ImmutableList;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTrace;
import com.microsoft.z3.Status;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.Map;
import java.util.concurrent.CountDownLatch;

public class ProcessBoundedExecutor<C extends Z3ContextWrapper<?, ?, ?, ?>> extends SMTExecutor {
    private final Schema<C> schema;
    private final ImmutableList<Policy> policies;
    private final QueryTrace queries;
    private ProcessSMTExecutor executor = null;
    private boolean shuttingDown = false;

    public ProcessBoundedExecutor(String name, CountDownLatch latch, Schema<C> schema, ImmutableList<Policy> policies, QueryTrace queries) {
        super(name, latch, true, false, false, false);
        this.schema = schema;
        this.policies = policies;
        this.queries = queries;
    }

    @Override
    protected Status doRunNormal() throws InterruptedException {
        // this sucks - this executor cannot exit even if we get a fast unsat, until initial bound estimation is done
         BoundEstimator<C> boundEstimator = new UnsatCoreBoundEstimator<>(new FixedBoundEstimator<>(0));
//        BoundEstimator boundEstimator = new FixedBoundEstimator(0);
        Map<String, Integer> bounds = boundEstimator.calculateBounds(schema, queries);

        while (!shuttingDown) {
            System.err.println(bounds);
            DeterminacyFormula<C, BoundedInstance<C>> boundedDeterminacyFormula = new BoundedDeterminacyFormula<>(schema, policies, bounds, true);
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
