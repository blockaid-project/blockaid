package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ListMultimap;
import com.google.common.collect.Maps;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;
import edu.berkeley.cs.netsys.privacy_proxy.util.LogLevel;
import edu.berkeley.cs.netsys.privacy_proxy.util.Options;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Logger.printMessage;

public class UnsatCoreBoundEstimator<C extends Z3ContextWrapper<?, ?, ?, ?>> extends BoundEstimator<C> {
    private Solver solver;
    private final BoundEstimator<C> initialEstimator;

    public UnsatCoreBoundEstimator(BoundEstimator<C> initialEstimator) {
        this.initialEstimator = initialEstimator;
    }

    @Override
    public Map<String, Integer> calculateBounds(Schema<C> schema, UnmodifiableLinearQueryTrace queries) {
        Map<String, Integer> initialBounds = new HashMap<>(initialEstimator.calculateBounds(schema, queries));
        ListMultimap<String, Map<String, Object>> knownRows = queries.computeKnownRows(schema.getRawSchema());

        Map<String, Integer> bounds = computeUpperBounds(schema, queries, knownRows, initialBounds);
        if (Options.SHRINK_BOUNDS == Options.OnOffType.ON) {
            bounds = shrinkBounds(schema, queries, knownRows, bounds);
        }
        return bounds;
    }

    private Map<String, Integer> computeUpperBounds(Schema<C> schema,
                                                    UnmodifiableLinearQueryTrace queries,
                                                    ListMultimap<String, Map<String, Object>> knownRows,
                                                    Map<String, Integer> initialBounds)
    {
        // Must create the solver after creating the formula, so that the solver contains assertions on constants
        // (e.g., distinct).
        solver = null;

        C context = schema.getContext();
        HashMap<String, Integer> bounds = new HashMap<>(initialBounds);

        int iter;
        for (iter = 0; ; ++iter) {
            BoundedInstance<C> instance = schema.makeBoundedInstance("inst", bounds, knownRows);

            ArrayList<NamedBoolExpr> assertions = new ArrayList<>();
            Map<BoolExpr, Dependency> dependencyLabels = new HashMap<>();
            int i = 0;
            for (Dependency d : schema.getDependencies()) {
                String name = "dependency!" + (i++);
                assertions.add(new NamedBoolExpr(d.apply(instance), name));
                dependencyLabels.put(context.mkBoolConst(name), d);
            }

            // add query constraints with labels
            i = 0;
            Map<BoolExpr, PrivacyQuery> queryLabels = new HashMap<>();
            for (QueryTraceEntry queryTraceEntry : queries.getAllEntries()) {
                PrivacyQuery query = queryTraceEntry.getQuery();
                Query<C> solverQuery = query.getSolverQuery(schema);
                Relation<C> r = solverQuery.apply(instance);

                List<Tuple<C>> tuples;
                if (queryTraceEntry.hasTuples()) {
                    tuples = DeterminacyFormula.getTupleObjects(queryTraceEntry, schema);
//                } else if (queryTraceEntry == queries.getCurrentQuery()) {
//                    // Insist that the current query returns at least one tuple.
//                    tuples = List.of(solverQuery.makeFreshHead());
                } else {
                    continue;
                }

                String name = "query!" + (i++);
                assertions.add(new NamedBoolExpr(r.doesContainExpr(tuples), name));
                queryLabels.put(context.mkBoolConst(name), query);
            }

            if (solver == null) {
                solver = schema.getContext().mkSolver();
                Params p = schema.getContext().mkParams();
                p.add("core.minimize", true);
                solver.setParameters(p);
            }
            solver.push();
            try {
                for (NamedBoolExpr e : assertions) {
                    solver.assertAndTrack(context.mkAnd(e.exprs()), context.mkBoolConst(e.name()));
                }

                // todo timeouts on this...
                long startNs = System.nanoTime();
                Status res = solver.check();
                long durNs = System.nanoTime() - startNs;
                printMessage("\t\t| bound estimator check (" + iter + "):\t" + durNs / 1000000, LogLevel.VERBOSE);
                if (res == Status.SATISFIABLE) {
                    break;
                }
                checkState(res == Status.UNSATISFIABLE, "solver returned: " + res);
                BoolExpr[] core = solver.getUnsatCore();

                Set<String> toIncrement = new HashSet<>();
                for (BoolExpr expr : core) {
                    if (dependencyLabels.containsKey(expr)) {
                        Dependency dependency = dependencyLabels.get(expr);
                        printMessage("\t\t\t" + dependency, LogLevel.VERBOSE);
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

                checkState(!toIncrement.isEmpty());
                for (String r : toIncrement) {
                    bounds.put(r, bounds.get(r) + 1);
                }
            } finally {
                solver.pop();
            }
        }
        printMessage(() -> "Initial bounds: " + Maps.filterEntries(bounds, e -> e.getValue() > 0), LogLevel.VERBOSE);
        return bounds;
    }

    private Map<String, Integer> shrinkBounds(Schema<C> schema,
                                              UnmodifiableLinearQueryTrace queries,
                                              ListMultimap<String, Map<String, Object>> knownRows,
                                              Map<String, Integer> initialBounds)
    {
        checkState(solver != null);
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

            // TODO(zhangwen): de-duplicate this code?
            List<Tuple<C>> tuples;
            if (queryTraceEntry.hasTuples()) {
                tuples = DeterminacyFormula.getTupleObjects(queryTraceEntry, schema);
//            } else if (queryTraceEntry == queries.getCurrentQuery()) {
//                tuples = List.of(solverQuery.makeFreshHead());
            } else {
                continue;
            }
            solver.add(context.mkAnd(r.doesContainExpr(tuples)));
        }
        checkArgument(solver.check() == Status.SATISFIABLE, "initial bounds not large enough");

        for (var entry : shrunkBounds.entrySet()) {
            String tableName = entry.getKey();
            int bound = entry.getValue();

            ConcreteRelation<C> rel = (ConcreteRelation<C>) instance.get(tableName);
            for (BoolExpr exists : rel.getExists()) {
                if (solver.check(context.mkNot(exists)) == Status.SATISFIABLE) {
                    solver.add(context.mkNot(exists));
                    bound -= 1;
                    printMessage("Shrinking bound for " + tableName + " to " + bound, LogLevel.VERBOSE);
                } else {
                    printMessage("Bound tight for " + tableName + " = " + bound, LogLevel.VERBOSE);
                    break;
                }
            }

            entry.setValue(bound);
        }

        return shrunkBounds;
    }
}
