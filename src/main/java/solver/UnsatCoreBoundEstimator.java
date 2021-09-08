package solver;

import cache.trace.QueryTraceEntry;
import cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.Iterables;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import sql.PrivacyQuery;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;

public class UnsatCoreBoundEstimator extends BoundEstimator {
    private final BoundEstimator initialBounds;

    public UnsatCoreBoundEstimator(BoundEstimator initialBounds) {
        this.initialBounds = initialBounds;
    }

    @Override
    public Map<String, Integer> calculateBounds(Schema schema, UnmodifiableLinearQueryTrace queries) {
        MyZ3Context context = schema.getContext();
        Map<String, Integer> bounds = new HashMap<>(initialBounds.calculateBounds(schema, queries));
        int iters;
        for (iters = 0; ; ++iters) {
            Solver solver = context.mkSolver();
            Params p = context.mkParams(); p.add("timeout", 1000); solver.setParameters(p);
            Instance instance = schema.makeConcreteInstance("inst", bounds,
                    queries.computeKnownRows(schema));

            Map<Constraint, Iterable<BoolExpr>> constraints = instance.getConstraints();
            Map<BoolExpr, Constraint> dependencyLabels = new HashMap<>();
            for (Map.Entry<Constraint, Iterable<BoolExpr>> constraint : constraints.entrySet()) {
                BoolExpr label = (BoolExpr) context.mkFreshConst("dependency", context.getBoolSort());
                solver.assertAndTrack(context.mkAnd(Iterables.toArray(constraint.getValue(), BoolExpr.class)), label);
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
                    BoolExpr expr = context.mkAnd(Iterables.toArray(r.doesContainExpr(tuples), BoolExpr.class));
                    BoolExpr label = (BoolExpr) context.mkFreshConst("query", context.getBoolSort());
                    solver.assertAndTrack(expr, label);
                    queryLabels.put(label, query);
                }
            }

            // todo timeouts on this...
//            long startMs = System.currentTimeMillis();
            Status res = solver.check();
//            long durMs = System.currentTimeMillis() - startMs;
//            System.out.println("\t\t| bound estimator check:\t" + durMs + "\t" + bounds);
            if (res == Status.SATISFIABLE) {
                break;
            }
            if (res != Status.UNSATISFIABLE) {
                System.out.println(bounds);
                try {
                    for (BoolExpr l : dependencyLabels.keySet()) solver.add(l);
                    for (BoolExpr l : queryLabels.keySet()) solver.add(l);
                    Files.write(Paths.get("/tmp/bound_estimator.smt2"), solver.toString().getBytes());
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
            }
            checkState(res == Status.UNSATISFIABLE, "solver returned: " + res);
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
//        System.out.println("\t\t| iterations: " + iters + ", bounds: " + bounds);
        return bounds;
    }
}
