package policy_checker;

import cache.*;
import cache.trace.QueryTrace;
import cache.trace.QueryTraceEntry;
import cache.trace.QueryTupleIdxPair;
import cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.*;
import com.microsoft.z3.*;
import org.apache.calcite.rel.type.*;
import org.apache.calcite.sql.type.SqlTypeFamily;
import solver.*;
import sql.PrivacyQuery;
import sql.SchemaPlusWithKey;
import util.Logger;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static util.Logger.printMessage;
import static util.TerminalColor.*;

public class QueryChecker {
    public static boolean ENABLE_CACHING = Objects.equals(System.getProperty("privoxy.enable_caching"), "true");
    public static boolean CACHE_NO_RETAIN = Objects.equals(System.getProperty("privoxy.cache_no_retain"), "true");
    public static boolean PRUNE_TRACE = true;
    public static boolean UNNAMED_EQUALITY = true;

    public enum PrecheckSetting {
        DISABLED,
        COARSE,
        FULL
    }

    public static PrecheckSetting PRECHECK_SETTING = PrecheckSetting.COARSE;

    private static final boolean PRINT_FORMULAS = Objects.equals(System.getProperty("privoxy.print_formulas"), "true");
    private static final String FORMULA_DIR = System.getenv("PRIVOXY_FORMULA_PATH");

    private static final int PREAPPROVE_MAX_PASSES = Integer.MAX_VALUE;

    private enum FastCheckDecision {
        ALLOW,
        DENY,
        UNKNOWN
    }

    public static long SOLVE_TIMEOUT_MS = 2000; // ms

    private final Schema schema;
    private final List<Policy> policySet;
    private final List<Query> policyQueries;

    private final SMTPortfolioRunner runner;
    private final DeterminacyFormula fastCheckDeterminacyFormula;
//    private final DeterminacyFormula determinacyFormula;
//    private final UnsatCoreDeterminacyFormula unsatCoreDeterminacyFormula;
//    private final UnsatCoreDeterminacyFormula unsatCoreDeterminacyFormulaEliminate;
    private final DecisionCache cache;

    private int queryCount; // Number of queries processed so far.
    private final DecisionTemplateGenerator dtg;

    /**
     * For sharing decision cache among `QueryChecker` objects for the same database / policy.
     */
    private static final ConcurrentHashMap<Properties, DecisionCache> decisionCaches = new ConcurrentHashMap<>();

    public QueryChecker(Properties info, ArrayList<Policy> policySet, SchemaPlusWithKey rawSchema,
                        List<Constraint> dependencies) {
        this.policySet = policySet;
        MyZ3Context context = new MyZ3Context();

        Map<String, List<Column>> relations = new HashMap<>();
        for (String tableName : rawSchema.schema.getTableNames()) {
            List<Column> columns = new ArrayList<>();
            for (RelDataTypeField field : rawSchema.getTypeForTable(tableName).getFieldList()) {
                Sort type = getSortFromSqlType(context, field.getType());
                // TODO(zhangwen): Other parts of the code seem to assume upper case table and column names (see
                //  ParsedPSJ.quantifyName), and so we upper case the column and table names here.  I hope this works.
                columns.add(new Column(field.getName().toUpperCase(), type));
            }
            relations.put(tableName.toUpperCase(), columns);
        }

        this.schema = new Schema(context, rawSchema, relations, dependencies);
        this.policyQueries = policySet.stream().map(p -> p.getSolverQuery(schema)).collect(Collectors.toList());

        this.runner = new SMTPortfolioRunner(this, SOLVE_TIMEOUT_MS);
//        this.determinacyFormula = new BasicDeterminacyFormula(schema, policyQueries);
        this.fastCheckDeterminacyFormula = new FastCheckDeterminacyFormula(schema, policyQueries);
//        this.unsatCoreDeterminacyFormula = new UnsatCoreDeterminacyFormula(schema, policySet, policyQueries, UNNAMED_EQUALITY, false);
//        this.unsatCoreDeterminacyFormulaEliminate = new UnsatCoreDeterminacyFormula(schema, policySet, policyQueries, UNNAMED_EQUALITY, true);
        this.dtg = new DecisionTemplateGenerator(this, schema, policySet, policyQueries,
                fastCheckDeterminacyFormula);

        // Find an existing cache corresponding to `info`, or create a new one if one doesn't exist already.
        this.cache = decisionCaches.computeIfAbsent(info, (Properties _info) -> new DecisionCache(schema, policySet));

        // Start custom sort value tracking for first query
        context.customSortsPush();
    }

    private static Sort getSortFromSqlType(MyZ3Context context, RelDataType type) {
        RelDataTypeFamily family = type.getFamily();
        if (family == SqlTypeFamily.NUMERIC) {
            // TODO(zhangwen): treating decimal also as int.
            switch (type.getSqlTypeName()) {
                case TINYINT:
                case SMALLINT:
                case INTEGER:
                case BIGINT:
                    return context.getCustomIntSort();
                case FLOAT:
                case REAL:
                case DOUBLE:
                    return context.getCustomRealSort();
            }
            throw new IllegalArgumentException("Unsupported numeric type: " + type);
        } else if (family == SqlTypeFamily.CHARACTER || family == SqlTypeFamily.BINARY) {
            return context.getCustomStringSort();
        } else if (family == SqlTypeFamily.TIMESTAMP) {
            return context.getTimestampSort();
        } else if (family == SqlTypeFamily.DATE) {
            return context.getDateSort();
        } else if (family == SqlTypeFamily.BOOLEAN) {
            return context.getCustomIntSort();
//            return context.mkBoolSort();
        } else if (family == SqlTypeFamily.ANY) {
            // FIXME(zhangwen): I think text belongs in here.
            return context.getCustomStringSort();
        }
        throw new IllegalArgumentException("unrecognized family: " + family);
    }

    public void resetSequence() {
        MyZ3Context context = schema.getContext();
        context.customSortsPop();
        context.customSortsPush();
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
        System.out.println("\t| Make fastSMT:\t" + (System.currentTimeMillis() - startTime));

        // regular check
//        startTime = System.currentTimeMillis();
//        String regularSMT = this.determinacyFormula.generateSMT(queries);
//        System.out.println("\t| Make regular:\t" + (System.currentTimeMillis() - startTime));
//        executors.add(new CVC4Executor("cvc4", regularSMT, latch, true, true, false));
//        printFormula(regularSMT, "regular", queries);

//        executors.add(new ProcessBoundedExecutor("z3_bounded_process", latch, schema, policyQueries, queries));

        return runner.checkFastUnsatFormula(fastCheckSMT, "fast_unsat");
    }

    private static class UnsatCore {
        private final ImmutableSet<String> labels;
        private final ImmutableMap<Object, Integer> equalityMap;

        public UnsatCore(Iterable<String> labels, Map<Object, Integer> equalityMap) {
            this.labels = ImmutableSet.copyOf(labels);
            this.equalityMap = ImmutableMap.copyOf(equalityMap);
        }
    }

//    private UnsatCore tryGetUnsatCore(QueryTrace queries) {
//        CountDownLatch latch = new CountDownLatch(4);
//        List<SMTExecutor> executors = new ArrayList<>();
//
//        String smt = this.unsatCoreDeterminacyFormula.generateSMT(queries);
//        Map<Object, Integer> equalityMap = this.unsatCoreDeterminacyFormula.getAssertionMap();
//        executors.add(new Z3Executor("z3_unsat", smt, latch));
//        executors.add(new CVC4Executor("cvc4_unsat", smt, latch));
//        printFormula(smt, "gen", queries);
//
//        smt = this.unsatCoreDeterminacyFormulaEliminate.generateSMT(queries);
//        Map<Object, Integer> equalityMapEliminate = this.unsatCoreDeterminacyFormulaEliminate.getAssertionMap();
//        executors.add(new Z3Executor("z3_unsat_eliminate", smt, latch));
//        executors.add(new CVC4Executor("cvc4_unsat_eliminate", smt, latch));
//        printFormula(smt, "gen_elim", queries);
//
//        runExecutors(executors, latch);
//
//        String[] minCore = null;
//        Map<Object, Integer> usedEqualityMap = null;
//        for (int i = 0; i < executors.size(); ++i) {
//            SMTExecutor executor = executors.get(i);
//            String[] core = executor.getUnsatCore();
//            if (core != null) {
//                System.err.println(Arrays.asList(core));
//            } else {
//                System.err.println("no result");
//            }
//            if (core != null && (minCore == null || minCore.length >= core.length)) {
//                minCore = core;
//                usedEqualityMap = (i < 2 ? equalityMap : equalityMapEliminate);
////                usedEqualityMap = equalityMapEliminate;
//            }
//        }
//
//        return minCore == null ? null : new UnsatCore(Arrays.asList(minCore), usedEqualityMap);
//    }

    private FastCheckDecision doPrecheckPolicy(PrivacyQuery query) {
        if (precheckPolicyApproval(query)) {
            return FastCheckDecision.ALLOW;
        }

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
            Optional<Collection<Integer>> oPkColIdxForPrune = qte.isEligibleForPruning(schema);
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

            seenPkValues.addAll(qte.getReturnedPkValues(schema));
        }

        return trace.getSubTrace(picked);
    }

    public boolean checkPolicy(QueryTrace queries) {
        queryCount += 1;

        PrivacyQuery currQuery = queries.getCurrentQuery().getQuery();
        printMessage(() -> "transformed: " + currQuery.parsedSql.getParsedSql()
                + "\t" + currQuery.parameters + "\t" + currQuery.paramNames
        );
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
                    cache.policyDecisionCacheFine.addCompliantToCache(currQuery.parsedSql.getParsedSql(),
                            currQuery.paramNames, dt);
                }
            }
//            cacheDecision(queries, policyResult);
            // FIXME(zhangwen): in case of noncompliance, find model.
            return true;
        } else {
            return doCheckPolicy(pickedTrace);
        }
    }

    /**
     * Caches a query decision. Equalities between fields (query parameters,
     * past query returned tuple cell values, and constants via SET) are only
     * considered if a query parameter is one of the fields. Values are not
     * considered for constants via SET -- it is assumed that the exact value
     * for these constants _never_ matters, and only equality against them is
     * relevant.
     */
//    private void cacheDecision(QueryTrace queries, boolean policyResult) {
//        UnsatCore core = null;
//        if (policyResult) {
//            core = tryGetUnsatCore(queries);
//        }
//        System.err.println("policy compliance: " + policyResult);
//        if (core == null) {
//            System.err.println("no core, not cached");
//            return;
//        }
//
//        QueryTraceEntry currQuery = queries.getCurrentQuery();
//
//        System.err.println("min core: " + core.labels);
//        CachedQueryTrace cacheTrace = new CachedQueryTrace();
//        int queryNumber = 0;
//        Set<Object> valueConstraints = new HashSet<>();
//        Set<Integer> paramAssertions = new HashSet<>();
//        Multiset<Integer> assertionOccurrences = HashMultiset.create();
//        // check used values, assertions
//        for (QueryTraceEntry queryEntry : queries.getAllEntries()) {
//            boolean keptQuery = core.labels.contains("a_q!" + queryNumber) || queryEntry == currQuery;
//            List<Object> parameters = queryEntry.getParameters();
//            for (int i = 0; i < parameters.size(); ++i) {
//                Object parameter = parameters.get(i);
//                if (core.labels.contains("a_pv!" + queryNumber + "!" + i)) {
//                    valueConstraints.add(parameter);
//                }
//                if (!keptQuery || !core.equalityMap.containsKey(parameter)) {
//                    continue;
//                }
//                int assertionNum = core.equalityMap.get(parameter);
//                if (UNNAMED_EQUALITY || core.labels.contains("a_e!" + assertionNum)) {
//                    paramAssertions.add(assertionNum);
//                    assertionOccurrences.add(assertionNum);
//                }
//            }
//
//            int attrNum = 0;
//            for (List<Object> tuple : queryEntry.getTuples()) {
//                for (Object value : tuple) {
//                    if (core.labels.contains("a_v!" + queryNumber + "!" + attrNum)) {
//                        valueConstraints.add(value);
//                    }
//                    if (!keptQuery || !core.equalityMap.containsKey(value)) {
//                        ++attrNum;
//                        continue;
//                    }
//                    int assertionNum = core.equalityMap.get(value);
//                    if (UNNAMED_EQUALITY || core.labels.contains("a_e!" + assertionNum)) {
//                        assertionOccurrences.add(assertionNum);
//                    }
//                    ++attrNum;
//                }
//            }
//            ++queryNumber;
//        }
//        for (Integer value : queries.getConstMap().values()) {
//            if (core.equalityMap.containsKey(value)) {
//                int assertionNum = core.equalityMap.get(value);
//                if (UNNAMED_EQUALITY || core.labels.contains("a_e!" + assertionNum)) {
//                    assertionOccurrences.add(assertionNum);
//                }
//            }
//        }
//
//        queryNumber = 0;
//        // generate cache entry
//        for (QueryTraceEntry queryEntry : queries.getAllEntries()) {
//            if (!core.labels.contains("a_q!" + queryNumber) && queryEntry != currQuery) {
//                ++queryNumber;
//                continue;
//            }
//            // equalities
//            List<Integer> parameterEquality = new ArrayList<>();
//            for (Object parameter : queryEntry.getParameters()) {
//                if (!core.equalityMap.containsKey(parameter)) {
//                    parameterEquality.add(null);
//                    continue;
//                }
//                int assertionNum = core.equalityMap.get(parameter);
//                if (paramAssertions.contains(assertionNum) && assertionOccurrences.count(assertionNum) > 1) {
//                    parameterEquality.add(assertionNum);
//                } else {
//                    parameterEquality.add(null);
//                }
//            }
//            List<List<Integer>> tupleEquality = new ArrayList<>();
//            for (List<Object> tuple : queryEntry.getTuples()) {
//                List<Integer> indices = new ArrayList<>();
//                for (Object value : tuple) {
//                    if (!core.equalityMap.containsKey(value)) {
//                        indices.add(null);
//                        continue;
//                    }
//                    int assertionNum = core.equalityMap.get(value);
//                    if (paramAssertions.contains(assertionNum) && assertionOccurrences.count(assertionNum) > 1) {
//                        indices.add(assertionNum);
//                    } else {
//                        indices.add(null);
//                    }
//                }
//                tupleEquality.add(indices);
//            }
//            // values
//            QueryTraceEntry processedQuery = new QueryTraceEntry(queryEntry);
//            List<Object> parameters = processedQuery.getParameters();
//            for (int i = 0; i < parameters.size(); ++i) {
//                if (!valueConstraints.contains(parameters.get(i))) {
//                    parameters.set(i, null);
//                }
//            }
//            for (List<Object> tuple : processedQuery.getTuples()) {
//                for (int j = 0; j < tuple.size(); ++j) {
//                    if (!valueConstraints.contains(tuple.get(j))) {
//                        tuple.set(j, null);
//                    }
//                }
//            }
//            CachedQueryTraceEntry entry = new CachedQueryTraceEntry(processedQuery, queryEntry == currQuery, parameterEquality, tupleEquality);
//            if (!entry.isEmpty()) {
//                cacheTrace.addEntry(entry);
//            }
//            ++queryNumber;
//        }
//        for (Map.Entry<String, Integer> c : queries.getConstMap().entrySet()) {
//            String name = c.getKey();
//            Integer value = c.getValue();
//            if (!core.equalityMap.containsKey(value)) {
//                cacheTrace.addVariable(name, null);
//                continue;
//            }
//            int assertionNum = core.equalityMap.get(value);
//            // TODO is it ok to ignore equalities solely between constants and maybe tuple values?
//            if (paramAssertions.contains(assertionNum) && assertionOccurrences.count(assertionNum) > 1) {
//                cacheTrace.addVariable(name, assertionNum);
//            } else {
//                cacheTrace.addVariable(name, null);
//            }
//        }
//        System.err.println(cacheTrace);
//        cache.policyDecisionCacheFine.addCompliantToCache(currQuery.getParsedSql(), currQuery.getQuery().paramNames, cacheTrace, policyResult);
//    }

    // The fields of `DecisionCache` are shared between `QueryChecker` objects for the same database & policy.
    private static class DecisionCache {
        final ImmutableList<ImmutableSet<String>> preapprovedSets;
        final TraceCache policyDecisionCacheFine;

        public DecisionCache(Schema schema, ArrayList<Policy> policySet) {
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
        private static ImmutableList<ImmutableSet<String>> buildPreapprovedSetsCoarse(ArrayList<Policy> policySet) {
            // FIXME(zhangwen): should we use normalized column names here?
            return policySet.stream().filter(Policy::hasNoTheta)
                    .map(policy -> ImmutableSet.copyOf(policy.getProjectColumns()))
                    .collect(ImmutableList.toImmutableList());
        }

        private static ImmutableList<ImmutableSet<String>> buildPreapprovedSetsFull(
                Schema schema, ArrayList<Policy> policySet) {
            class Entry {
                private final BoolExpr predicate;
                private final ImmutableSet<String> columns;

                public Entry(BoolExpr predicate, ImmutableSet<String> columns) {
                    this.predicate = predicate;
                    this.columns = columns;
                }
            }

            MyZ3Context ctx = schema.getContext();

            ImmutableList.Builder<ImmutableSet<String>> preapprovedSetsBuilder = ImmutableList.builder();

            Map<Set<Integer>, Entry> previousPass = new HashMap<>();
            previousPass.put(Collections.emptySet(), new Entry(ctx.mkBool(false), getAllColumns(policySet)));

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

                                Solver solver = ctx.mkSolver();
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

        private static ImmutableSet<String> getAllColumns(ArrayList<Policy> policySet) {
            return policySet.stream()
                    .flatMap(policy -> policy.getProjectColumns().stream())
                    .collect(ImmutableSet.toImmutableSet());
        }
    }
}
