package edu.berkeley.cs.netsys.privacy_proxy.solver.executor;

import com.google.common.collect.ImmutableList;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTrace;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.Map;
import java.util.concurrent.CountDownLatch;

public class BoundedExecutor<C extends Z3ContextWrapper<?, ?, ?, ?>> extends SMTExecutor {
    private final Schema<C> schema;
    private final ImmutableList<Policy> policies;
    private final QueryTrace queries;
    private Solver solver;
    private boolean shuttingDown = false;

    public BoundedExecutor(String name, CountDownLatch latch, Schema<C> schema, ImmutableList<Policy> policies, QueryTrace queries) {
        super(name, latch, true, false, false, false);
        this.schema = schema;
        this.policies = policies;
        this.queries = queries;
    }

    @Override
    protected Status doRunNormal() {
        long startTime = System.currentTimeMillis();

        C context = schema.getContext();
        // this sucks - this executor cannot exit even if we get a fast unsat, until formula generation is done
        BoundEstimator<C> boundEstimator = new UnsatCoreBoundEstimator<>(new FixedBoundEstimator<>(0));
        Map<String, Integer> bounds = boundEstimator.calculateBounds(schema, queries);
        BoundedDeterminacyFormula<C> boundedDeterminacyFormula = new BoundedDeterminacyFormula<>(schema, policies, bounds, true);

        synchronized (this) {
            if (shuttingDown) {
                return Status.UNKNOWN;
            }
            solver = context.mkSolver();
            for (BoolExpr expr : boundedDeterminacyFormula.makeBodyFormula(queries)) {
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
