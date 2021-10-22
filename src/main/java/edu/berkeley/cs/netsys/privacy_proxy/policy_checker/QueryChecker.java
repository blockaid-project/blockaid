package edu.berkeley.cs.netsys.privacy_proxy.policy_checker;

import edu.berkeley.cs.netsys.privacy_proxy.cache.*;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTrace;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTupleIdxPair;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.*;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;
import edu.berkeley.cs.netsys.privacy_proxy.sql.SchemaPlusWithKey;
import edu.berkeley.cs.netsys.privacy_proxy.util.Logger;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Logger.printMessage;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.*;
import static edu.berkeley.cs.netsys.privacy_proxy.util.TerminalColor.*;

public class QueryChecker {
    public static boolean PRUNE_TRACE = true;
    public static boolean UNNAMED_EQUALITY = true;

    public enum PrecheckSetting {
        DISABLED,
        COARSE,
        FULL
    }

    public static PrecheckSetting PRECHECK_SETTING = PrecheckSetting.COARSE;

    private static final int PREAPPROVE_MAX_PASSES = Integer.MAX_VALUE;

    private enum FastCheckDecision {
        ALLOW,
        DENY,
        UNKNOWN
    }

    public static long SOLVE_TIMEOUT_MS = 2000; // ms

    private final SchemaPlusWithKey rawSchema;
    private final List<Policy> policySet;

    private final Schema customSortsSchema;
    private final Schema theorySchema;
    private final ImmutableList<Schema> allSchemata;

    private final SMTPortfolioRunner runner;
    private final DeterminacyFormula fastCheckDeterminacyFormula;
//    private final DeterminacyFormula determinacyFormula;
    private final DecisionCache cache;

    private int queryCount; // Number of queries processed so far.
    private final DecisionTemplateGenerator dtg;

    /**
     * For sharing decision cache among `QueryChecker` objects for the same database / policy.
     */
    private static final ConcurrentHashMap<Properties, DecisionCache> decisionCaches = new ConcurrentHashMap<>();

    public QueryChecker(Properties info, ImmutableList<Policy> policySet, SchemaPlusWithKey rawSchema,
                        List<Constraint> dependencies) {
        this.rawSchema = rawSchema;
        this.policySet = policySet;

        this.customSortsSchema = new Schema(Z3ContextWrapper.makeCustomSortsContext(), rawSchema, dependencies);
        this.theorySchema = new Schema(
                BOUNDED_USE_TYEORY ? Z3ContextWrapper.makeTheoryContext() : Z3ContextWrapper.makeCustomSortsContext(),
                rawSchema, dependencies);
        this.allSchemata = ImmutableList.of(customSortsSchema, theorySchema);

        this.runner = new SMTPortfolioRunner(this, SOLVE_TIMEOUT_MS);
//        this.determinacyFormula = new BasicDeterminacyFormula(customSortsSchema, policySet);
        this.fastCheckDeterminacyFormula = new FastCheckDeterminacyFormula(customSortsSchema, policySet);
        this.dtg = ENABLE_CACHING ?
                new DecisionTemplateGenerator(this, customSortsSchema, theorySchema,
                        policySet, fastCheckDeterminacyFormula)
                : null;

        // Find an existing cache corresponding to `info`, or create a new one if one doesn't exist already.
        this.cache = decisionCaches.computeIfAbsent(info, (Properties _info) ->
                // This schema is for building preapproved sets; shouldn't matter which one we use.
                new DecisionCache(customSortsSchema, policySet));

        // At this point, the context should be tracking all constants from the views and constraints.
        // Call `push` to separate them from the trace-specific constants.
        for (Schema schema : allSchemata) {
            schema.getContext().pushTrackConsts();
        }
    }


    public void resetSequence() {
        for (Schema schema : allSchemata) {
            Z3ContextWrapper context = schema.getContext();
            context.popTrackConsts();
            context.pushTrackConsts();
        }
        if (CLEAR_CACHE_AT_RESET) {
            cache.policyDecisionCacheFine.clear();
        }
        queryCount = 0;
    }

    private boolean precheckPolicyApproval(PrivacyQuery query) {
        Set<String> projectColumns = query.getAllNormalizedProjectColumns();
        List<String> thetaColumns = query.getThetaColumns();

        for (Set<String> s : cache.preapprovedSets) {
            if (s.containsAll(projectColumns) && s.containsAll(thetaColumns)) {
                return true;
            }
        }
        return false;
    }

    private boolean precheckPolicyDenial(PrivacyQuery query, Policy policy) {
        return !policy.checkApplicable(new HashSet<>(query.getAllNormalizedProjectColumns()), new HashSet<>(query.getThetaColumns()));
    }

    /**
     * If the option to print formulas is enabled, prints the formula to a file named `[prefix]_[index].smt2`.
     * @param formula the formula to print.
     * @param fileNamePrefix the prefix of the file name.
     */
    public void printFormula(String formula, String fileNamePrefix) {
        if (PRINT_FORMULAS) {
            try {
                String path = String.format("%s/%s_%d.smt2", FORMULA_DIR, fileNamePrefix, queryCount - 1);
                Files.write(Paths.get(path), formula.getBytes());
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }

    public void printFormula(Supplier<String> mkFormula, String fileNamePrefix) {
        if (PRINT_FORMULAS) {
            printFormula(mkFormula.get(), fileNamePrefix);
        }
    }

    private boolean doCheckPolicy(UnmodifiableLinearQueryTrace queries) {
//        BoundEstimator boundEstimator = new UnsatCoreBoundEstimator(new CountingBoundEstimator());
//        Map<String, Integer> bounds = boundEstimator.calculateBounds(schema, queries);
//        Map<String, Integer> slackBounds = Maps.transformValues(bounds, n -> n + 2);
//        BoundedDeterminacyFormula bdf = new BoundedDeterminacyFormula(schema, policyQueries, slackBounds,
//                false, DeterminacyFormula.TextOption.NO_TEXT, queries.computeKnownRows(schema));
//        Solver solver = schema.getContext().mkSolver();
//        return solver.check(Iterables.toArray(bdf.makeCompleteFormula(queries), BoolExpr.class)) == Status.UNSATISFIABLE;

        // fast check
        long startTime = System.currentTimeMillis();
        String fastCheckSMT = this.fastCheckDeterminacyFormula.generateSMT(queries);
        printMessage("\t| Make fastSMT:\t" + (System.currentTimeMillis() - startTime));

        // regular check
//        startTime = System.currentTimeMillis();
//        String regularSMT = this.determinacyFormula.generateSMT(queries);
//        System.out.println("\t| Make regular:\t" + (System.currentTimeMillis() - startTime));
//        executors.add(new CVC4Executor("cvc4", regularSMT, latch, true, true, false));
//        printFormula(regularSMT, "regular", queries);

//        executors.add(new ProcessBoundedExecutor("z3_bounded_process", latch, schema, policyQueries, queries));

        return runner.checkFastUnsatFormula(fastCheckSMT, "fast_unsat");
    }

    private FastCheckDecision doPrecheckPolicy(PrivacyQuery query) {
        if (precheckPolicyApproval(query)) {
            return FastCheckDecision.ALLOW;
        }

        if (ENABLE_QUICK_DENIAL) {
            boolean anyApplicable = false;
            for (Policy policy : policySet) {
                if (!precheckPolicyDenial(query, policy)) {
                    anyApplicable = true;
                    break;
                }
            }

            if (!anyApplicable) {
                return FastCheckDecision.DENY;
            }
        }

        return FastCheckDecision.UNKNOWN;
    }

    /**
     * Picks entries in the trace that are likely relevant to the current query's compliance.
     * @param trace the entire trace.
     * @return the sub-trace.
     */
    private UnmodifiableLinearQueryTrace pickTrace(QueryTrace trace) {
        QueryTraceEntry checkedEntry = trace.getCurrentQuery();
        checkArgument(checkedEntry != null, "there must be a query being checked");
        List<Object> checkedQueryParams = checkedEntry.getParameters();

        List<QueryTraceEntry> allEntries = trace.getAllEntries();
        HashSet<Integer> seenPkValues = new HashSet<>();
        ArrayList<QueryTupleIdxPair> picked = new ArrayList<>();
        for (int queryIdx = 0; queryIdx < allEntries.size(); ++queryIdx) {
            QueryTraceEntry qte = allEntries.get(queryIdx);
            if (!qte.hasTuples()) {
                continue;
            }

            List<List<Object>> tuples = qte.getTuples();
            Optional<Collection<Integer>> oPkColIdxForPrune = qte.isEligibleForPruning(rawSchema);
            if (oPkColIdxForPrune.isEmpty()) { // Keep them all.
                for (int tupIdx = 0; tupIdx < tuples.size(); ++tupIdx) {
                    picked.add(new QueryTupleIdxPair(queryIdx, tupIdx));
                }
            } else {
//                System.out.println("=== pruning ===");
//                System.out.println(qte.getParsedSql());
                Collection<Integer> pkColIdxForPrune = oPkColIdxForPrune.get();
                checkState(!pkColIdxForPrune.isEmpty());
                for (int tupIdx = 0; tupIdx < tuples.size(); ++tupIdx) {
                    boolean kept = false;
                    List<Object> tup = tuples.get(tupIdx);
                    for (int colIdx : pkColIdxForPrune) {
                        Object v = tup.get(colIdx);
//                        System.out.println("\tlooking:\t" + v);
                        if (checkedQueryParams.contains(v) && !seenPkValues.contains(v)) { // TODO(zhangwen): this is a hack.
                            picked.add(new QueryTupleIdxPair(queryIdx, tupIdx));
                            kept = true;
                            break;
                        }
                    }
                    if (kept) {
//                        System.out.println("\tkept:\t" + tuples.get(tupIdx));
                    }
                }
//                System.out.println("=== done ===");
            }

            seenPkValues.addAll(qte.getReturnedPkValues(rawSchema));
        }

        return trace.getSubTrace(picked);
    }

    public boolean checkPolicy(QueryTrace queries) {
        queryCount += 1;

        PrivacyQuery currQuery = queries.getCurrentQuery().getQuery();
//        printMessage(() -> "transformed: " + currQuery.parsedSql.getParsedSql()
//                + "\t" + currQuery.parameters + "\t" + currQuery.paramNames
//        );

        if (SKIP_CHECKING) {
            return true;
        }

        if (PRECHECK_SETTING != PrecheckSetting.DISABLED) {
            FastCheckDecision precheckResult = doPrecheckPolicy(currQuery);
            if (precheckResult == FastCheckDecision.ALLOW) {
                return true;
            }
            if (precheckResult == FastCheckDecision.DENY && queries.size() == 1) {
                // fast check deny will reject queries that depend on past data
                return false;
            }
        }
        if (ENABLE_CACHING) {
            Boolean cacheResult = cache.policyDecisionCacheFine.checkCache(queries);
            if (cacheResult != null) {
                return cacheResult;
            }
        }

        // Cache miss.  Check compliance!
        UnmodifiableLinearQueryTrace pickedTrace = PRUNE_TRACE ? pickTrace(queries) : queries;
//        System.out.println(pickedTrace);
        if (ENABLE_CACHING) {
            System.out.println("\t| Generate decision template:");
            Optional<Collection<DecisionTemplate>> oTemplates = dtg.generate(pickedTrace);
            if (oTemplates.isEmpty()) {
                return false;
            }
            for (DecisionTemplate dt : oTemplates.get()) {
                Logger.printStylizedMessage(dt.toString(), ANSI_BLACK + ANSI_YELLOW_BACKGROUND);
                if (!CACHE_NO_RETAIN) {
                    cache.policyDecisionCacheFine.addCompliantToCache(currQuery.parserResult, currQuery.paramNames, dt);
                }
            }
//            cacheDecision(queries, policyResult);
            // FIXME(zhangwen): in case of noncompliance, find model.
            return true;
        } else {
            return doCheckPolicy(pickedTrace);
        }
    }

    // The fields of `DecisionCache` are shared between `QueryChecker` objects for the same database & policy.
    private static class DecisionCache {
        final ImmutableList<ImmutableSet<String>> preapprovedSets;
        final TraceCache policyDecisionCacheFine;

        public DecisionCache(Schema schema, List<Policy> policySet) {
            switch (PRECHECK_SETTING) {
                case DISABLED -> this.preapprovedSets = null;
                case COARSE -> this.preapprovedSets = buildPreapprovedSetsCoarse(policySet);
                case FULL -> this.preapprovedSets = buildPreapprovedSetsFull(schema, policySet);
                default -> throw new IllegalStateException("invalid precheck setting: " + PRECHECK_SETTING);
            }
            this.policyDecisionCacheFine = new TraceCache();
        }

        /**
         * Returns the projected columns of each policy that has no `WHERE` clause.
         * @param policySet the set of policies from which to build the preapproved set.
         * @return the preapproved set.
         */
        private static ImmutableList<ImmutableSet<String>> buildPreapprovedSetsCoarse(List<Policy> policySet) {
            // FIXME(zhangwen): should we use normalized column names here?
            return policySet.stream().filter(Policy::hasNoTheta)
                    .map(policy -> ImmutableSet.copyOf(policy.getProjectColumns()))
                    .collect(ImmutableList.toImmutableList());
        }

        private static ImmutableList<ImmutableSet<String>> buildPreapprovedSetsFull(
                Schema schema, List<Policy> policySet) {
            class Entry {
                private final BoolExpr predicate;
                private final ImmutableSet<String> columns;

                public Entry(BoolExpr predicate, ImmutableSet<String> columns) {
                    this.predicate = predicate;
                    this.columns = columns;
                }
            }

            Z3ContextWrapper ctx = schema.getContext();

            ImmutableList.Builder<ImmutableSet<String>> preapprovedSetsBuilder = ImmutableList.builder();

            Map<Set<Integer>, Entry> previousPass = new HashMap<>();
            previousPass.put(Collections.emptySet(), new Entry(ctx.mkFalse(), getAllColumns(policySet)));

            Map<Set<Integer>, Entry> currentPass;

            for (int i = 1; i <= policySet.size() && i <= PREAPPROVE_MAX_PASSES && !previousPass.isEmpty(); ++i) {
                currentPass = new HashMap<>();

                Set<Set<Integer>> remove = new HashSet<>();
                for (Map.Entry<Set<Integer>, Entry> e : previousPass.entrySet()) {
                    Set<Integer> prevSet = e.getKey();
                    Entry entry = e.getValue();
                    BoolExpr prevPredicate = entry.predicate;
                    Set<String> prevColumns = entry.columns;

                    for (int j = 0; j < policySet.size(); ++j) {
                        if (prevSet.contains(j)) {
                            continue;
                        }

                        Set<Integer> nextSet = new HashSet<>(prevSet);
                        nextSet.add(j);

                        if (prevPredicate == null) {
                            // previous set was added to preapprovedSet
                            remove.add(nextSet);
                        } else if (!currentPass.containsKey(nextSet)) {
                            Sets.SetView<String> nextColumns = Sets.intersection(prevColumns, policySet.get(j).getProjectColumns());

                            if (!nextColumns.isEmpty()) {
                                BoolExpr nextPredicate = ctx.mkOr(prevPredicate, policySet.get(j).getPredicate(schema));

                                Solver solver = ctx.mkRawSolver();
                                solver.add(ctx.mkNot(nextPredicate));
                                Status q = solver.check();
                                boolean predicateResult = (q == Status.UNSATISFIABLE);
                                currentPass.put(nextSet, new Entry(predicateResult ? null : nextPredicate, nextColumns.immutableCopy()));
                            }
                        }
                    }
                }

                for (Set<Integer> s : remove) {
                    currentPass.remove(s);
                }

                for (Map.Entry<Set<Integer>, Entry> entry : currentPass.entrySet()) {
                    if (entry.getValue().predicate == null) {
                        preapprovedSetsBuilder.add(entry.getValue().columns);
                    }
                }

                previousPass = currentPass;
            }

            return preapprovedSetsBuilder.build();
        }

        private static ImmutableSet<String> getAllColumns(Collection<Policy> policySet) {
            return policySet.stream()
                    .flatMap(policy -> policy.getProjectColumns().stream())
                    .collect(ImmutableSet.toImmutableSet());
        }
    }
}
