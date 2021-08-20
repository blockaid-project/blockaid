package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import sql.PrivacyQuery;

import java.util.*;
import java.util.stream.Collectors;

public class UnsatCoreBoundEstimator extends BoundEstimator {
    private final BoundEstimator initialBounds;

    public UnsatCoreBoundEstimator() {
        this.initialBounds = new FixedBoundEstimator(0);
    }

    public UnsatCoreBoundEstimator(BoundEstimator initialBounds) {
        this.initialBounds = initialBounds;
    }

    @Override
    public Map<String, Integer> calculateBounds(Schema schema, QueryTrace queries) {
        Map<String, Integer> bounds = new HashMap<>(initialBounds.calculateBounds(schema, queries));
        int iters = 0;
        boolean unsat;
        do {
            MyZ3Context context = schema.getContext();
            Solver solver = context.mkSolver();
            Instance instance = schema.makeConcreteInstance("inst", bounds);

            Map<Constraint, BoolExpr> constraints = instance.getConstraints();
            Map<BoolExpr, Constraint> dependencyLabels = new HashMap<>();
            for (Map.Entry<Constraint, BoolExpr> constraint : constraints.entrySet()) {
                BoolExpr label = (BoolExpr) context.mkFreshConst("dependency", context.getBoolSort());
                solver.assertAndTrack(constraint.getValue(), label);
                dependencyLabels.put(label, constraint.getKey());
            }

            // add query constraints with labels
            Map<BoolExpr, PrivacyQuery> queryLabels = new HashMap<>();
            for (QueryTraceEntry queryTraceEntry : queries.getAllEntries()) {
                PrivacyQuery query = queryTraceEntry.getQuery();
                Query solverQuery = query.getSolverQuery(schema);
                Relation r = solverQuery.apply(instance);
                if (queryTraceEntry.hasTuples()) {
                    List<Tuple> tuples = queryTraceEntry.getTuplesStream().map(
                            tuple -> new Tuple(schema, tuple.stream().map(
                                    v -> Tuple.getExprFromObject(context, v)
                            ))).collect(Collectors.toList());
                    BoolExpr expr = r.doesContainExpr(tuples);
                    BoolExpr label = (BoolExpr) context.mkFreshConst("query", context.getBoolSort());
                    solver.assertAndTrack(expr, label);
                    queryLabels.put(label, query);
                }
            }

            // todo timeouts on this...
            unsat = (solver.check() == Status.UNSATISFIABLE);
            if (unsat) {
                BoolExpr[] core = solver.getUnsatCore();
                Set<String> toIncrement = new HashSet<>();
                for (BoolExpr expr : core) {
                    if (dependencyLabels.containsKey(expr)) {
                        Constraint dependency = dependencyLabels.get(expr);
                        if (dependency instanceof Dependency) {
                            Dependency d = (Dependency) dependency;
                            toIncrement.addAll(d.getToRelations());
                        }
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
            }
            ++iters;
        } while (unsat);
        System.out.println("\t\t| iterations: " + iters + ", bounds: " + bounds);
        return bounds;
    }
}
