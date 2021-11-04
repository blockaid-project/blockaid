package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ListMultimap;
import com.microsoft.z3.Model;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;
import edu.berkeley.cs.netsys.privacy_proxy.util.LogLevel;
import edu.berkeley.cs.netsys.privacy_proxy.util.Logger;
import edu.berkeley.cs.netsys.privacy_proxy.util.Options;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class UnsatCoreBoundEstimator<C extends Z3ContextWrapper<?, ?, ?, ?>> extends BoundEstimator<C> {
    private final BoundEstimator<C> initialEstimator;

    public UnsatCoreBoundEstimator(BoundEstimator<C> initialEstimator) {
        this.initialEstimator = initialEstimator;
    }

    @Override
    public Map<String, Integer> calculateBounds(Schema<C> schema, UnmodifiableLinearQueryTrace queries) {
        Map<String, Integer> initialBounds = new HashMap<>(initialEstimator.calculateBounds(schema, queries));
        ListMultimap<String, Map<String, Object>> knownRows = queries.computeKnownRows(schema.getRawSchema());

        Solver solver = schema.getContext().mkSolver();
        Map<String, Integer> bounds = computeUpperBounds(schema, queries, knownRows, solver, initialBounds);
        if (Options.SHRINK_BOUNDS == Options.OnOffType.ON) {
            bounds = shrinkBounds(schema, queries, knownRows, solver, bounds);
        }
        return bounds;
    }

    private Map<String, Integer> computeUpperBounds(Schema<C> schema,
                                                    UnmodifiableLinearQueryTrace queries,
                                                    ListMultimap<String, Map<String, Object>> knownRows,
                                                    Solver solver,
                                                    Map<String, Integer> initialBounds) {
        C context = schema.getContext();
        HashMap<String, Integer> bounds = new HashMap<>(initialBounds);

        int iters;
        for (iters = 0; ; ++iters) {
            BoundedInstance<C> instance = schema.makeBoundedInstance("inst", bounds, knownRows);

            ArrayList<NamedBoolExpr> assertions = new ArrayList<>();
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

    private Map<String, Integer> shrinkBounds(Schema<C> schema,
                                              UnmodifiableLinearQueryTrace queries,
                                              ListMultimap<String, Map<String, Object>> knownRows,
                                              Solver solver,
                                              Map<String, Integer> initialBounds)
    {
        C context = schema.getContext();
        BoundedInstance<C> instance = schema.makeBoundedInstance("inst", initialBounds, knownRows);
        HashMap<String, Integer> shrunkBounds = new HashMap<>(initialBounds);

        for (Dependency d : schema.getDependencies()) {
            solver.add(context.mkAnd(d.apply(instance)));
        }
        for (QueryTraceEntry queryTraceEntry : queries.getAllEntries()) {
            PrivacyQuery query = queryTraceEntry.getQuery();
            Query<C> solverQuery = query.getSolverQuery(schema);
            Relation<C> r = solverQuery.apply(instance);
            if (queryTraceEntry.hasTuples()) {
                List<Tuple<C>> tuples = DeterminacyFormula.getTupleObjects(queryTraceEntry, schema);
                solver.add(context.mkAnd(r.doesContainExpr(tuples)));
            }
        }
        checkArgument(solver.check() == Status.SATISFIABLE, "initial bounds not large enough");

        Logger.printMessage(() -> {
            StringBuilder sb = new StringBuilder();
            Model m = solver.getModel();
            for (var entry : shrunkBounds.entrySet()) {
                if (entry.getValue() == 0) {
                    continue;
                }

                String pks = ((ConcreteRelation<C>) instance.get(entry.getKey())).getTuples().stream()
                        .map(t -> m.eval(t.get(0), false).toString())
                        .collect(Collectors.joining(", "));
                sb.append(entry.getKey()).append("\t").append(pks).append("\n");
            }
            return sb.toString();
        }, LogLevel.VERBOSE);

        for (var entry : shrunkBounds.entrySet()) {
            String tableName = entry.getKey();
            int bound = entry.getValue();

            ConcreteRelation<C> rel = (ConcreteRelation<C>) instance.get(tableName);
            for (BoolExpr exists : rel.getExists()) {
                if (solver.check(context.mkNot(exists)) == Status.SATISFIABLE) {
                    solver.add(context.mkNot(exists));
                    bound -= 1;
                    Logger.printMessage("Shrinking bound for " + tableName + " to " + bound, LogLevel.VERBOSE);
                } else {
                    Logger.printMessage("Bound tight for " + tableName + " = " + bound, LogLevel.VERBOSE);
                    break;
                }
            }

            entry.setValue(bound);
        }

        return shrunkBounds;
    }
}
