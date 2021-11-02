package edu.berkeley.cs.netsys.privacy_proxy.solver;

import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;

public class UnsatCoreBoundEstimator<C extends Z3ContextWrapper<?, ?, ?, ?>> extends BoundEstimator<C> {
    private final BoundEstimator<C> initialBounds;
    private Solver solver;

    public UnsatCoreBoundEstimator(BoundEstimator<C> initialBounds) {
        this.initialBounds = initialBounds;
        this.solver = null;
    }

    @Override
    public Map<String, Integer> calculateBounds(Schema<C> schema, UnmodifiableLinearQueryTrace queries) {
        C context = schema.getContext();
        Map<String, Integer> bounds = new HashMap<>(initialBounds.calculateBounds(schema, queries));

        int iters;
        for (iters = 0; ; ++iters) {
            ArrayList<NamedBoolExpr> assertions = new ArrayList<>();

            Instance<C> instance = schema.makeConcreteInstance("inst", bounds,
                    queries.computeKnownRows(schema.getRawSchema()));

            Map<BoolExpr, Dependency> dependencyLabels = new HashMap<>();
            int i = 0;
            for (Dependency d : schema.getDependencies()) {
                String name = "dependency!" + (i++);
                assertions.add(new NamedBoolExpr(context.mkAnd(d.apply(instance)), name));
                dependencyLabels.put(context.mkBoolConst(name), d);
            }

            // add query constraints with labels
            i = 0;
            Map<BoolExpr, PrivacyQuery> queryLabels = new HashMap<>();
            for (QueryTraceEntry queryTraceEntry : queries.getAllEntries()) {
                PrivacyQuery query = queryTraceEntry.getQuery();
                Query<C> solverQuery = query.getSolverQuery(schema);
                Relation<C> r = solverQuery.apply(instance);
                if (queryTraceEntry.hasTuples()) {
                    List<Tuple<C>> tuples = DeterminacyFormula.getTupleObjects(queryTraceEntry, schema);
                    String name = "query!" + (i++);
                    assertions.add(new NamedBoolExpr(context.mkAnd(r.doesContainExpr(tuples)), name));
                    queryLabels.put(context.mkBoolConst(name), query);
                }
            }

            if (solver == null) {
                // Only need to make the solver once, because the constants never change.
                solver = context.mkSolver();
            }
            solver.push();
            try {
                for (NamedBoolExpr e : assertions) {
                    solver.assertAndTrack(e.expr(), context.mkBoolConst(e.name()));
                }

                // todo timeouts on this...
//            long startMs = System.currentTimeMillis();
                Status res = solver.check();
//            long durMs = System.currentTimeMillis() - startMs;
//            System.out.println("\t\t| bound estimator check:\t" + durMs + "\t" + bounds);
                if (res == Status.SATISFIABLE) {
                    break;
                }
                checkState(res == Status.UNSATISFIABLE, "solver returned: " + res);
                BoolExpr[] core = solver.getUnsatCore();

                Set<String> toIncrement = new HashSet<>();
                for (BoolExpr expr : core) {
                    if (dependencyLabels.containsKey(expr)) {
                        Dependency dependency = dependencyLabels.get(expr);
                        toIncrement.addAll(dependency.getToRelations());
                    }
                }

                if (toIncrement.isEmpty()) {
                    for (BoolExpr expr : core) {
                        if (queryLabels.containsKey(expr)) {
                            PrivacyQuery query = queryLabels.get(expr);
                            toIncrement.addAll(query.getRelations());
                        }
                    }
                }

                assert !toIncrement.isEmpty();
                for (String r : toIncrement) {
                    bounds.put(r, bounds.get(r) + 1);
                }
            } finally {
                solver.pop();
            }
        }
//        System.out.println("\t\t| iterations: " + iters + ", bounds: " + bounds);
        return bounds;
    }

    public Solver getSolver() {
        return Objects.requireNonNull(solver);
    }
}
