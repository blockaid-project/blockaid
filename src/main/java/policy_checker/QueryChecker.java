package policy_checker;

import cache.*;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import com.microsoft.z3.*;
import planner.PrivacyColumn;
import planner.PrivacyTable;
import solver.*;
import solver.executor.*;
import sql.Parser;
import sql.PrivacyQuery;
import sql.SchemaPlusWithKey;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.io.PrintWriter;
import java.sql.SQLException;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

public class QueryChecker {
    public static boolean ENABLE_CACHING = true;
    public static boolean UNNAMED_EQUALITY = true;

    public enum PrecheckSetting {
        DISABLED,
        COARSE,
        FULL
    }

    public static PrecheckSetting PRECHECK_SETTING = PrecheckSetting.COARSE;

    private static final boolean PRINT_FORMULAS = false;
    private static final String FORMULA_DIR = System.getenv("PRIVOXY_FORMULA_PATH");

    private static final int PREAPPROVE_MAX_PASSES = Integer.MAX_VALUE;

    private enum FastCheckDecision {
        ALLOW,
        DENY,
        UNKNOWN
    }

    public static long SOLVE_TIMEOUT = 20000; // ms

    private final Schema schema;
    private final ArrayList<Policy> policySet;
    private final DeterminacyFormula fastCheckDeterminacyFormula;
    private final DeterminacyFormula determinacyFormula;
    private final DeterminacyFormula boundedDeterminacyFormula;
    private final UnsatCoreDeterminacyFormula unsatCoreDeterminacyFormula;
    private final UnsatCoreDeterminacyFormula unsatCoreDeterminacyFormulaEliminate;
    private final DecisionCache cache;

    /**
     * For sharing decision cache among `QueryChecker` objects for the same database / policy.
     */
    private static final ConcurrentHashMap<Properties, DecisionCache> decisionCaches = new ConcurrentHashMap<>();

    public static QueryChecker getInstance(Properties info, Parser parser, ArrayList<Policy> policySet, SchemaPlusWithKey rawSchema,
                                           String[] deps, String[] uks, String[] fks) throws SQLException {
        return new QueryChecker(info, parser, policySet, rawSchema, deps, uks, fks);
    }

    private QueryChecker(Properties info, Parser parser, ArrayList<Policy> policySet, SchemaPlusWithKey rawSchema,
                         String[] deps, String[] uks, String[] fks) throws SQLException
    {
        this.policySet = policySet;
        MyZ3Context context = new MyZ3Context();

        Map<String, List<Column>> relations = new HashMap<>();
        for (String tableName : rawSchema.schema.getTableNames()) {
            PrivacyTable table = (PrivacyTable) rawSchema.schema.getTable(tableName);
            List<Column> columns = new ArrayList<>();
            for (PrivacyColumn column : table.getColumns()) {
                Sort type = Schema.getSortFromSqlType(context, column.type);
                // TODO(zhangwen): Other parts of the code seem to assume upper case table and column names (see
                //  ParsedPSJ.quantifyName), and so we upper case the column and table names here.  I hope this works.
                columns.add(new Column(column.name.toUpperCase(), type));
            }
            relations.put(tableName.toUpperCase(), columns);
        }

        List<Dependency> dependencies = new ArrayList<>();
        for (String uk : uks) {
            uk = uk.toUpperCase();
            String[] parts = uk.split(":", 2);
            String[] columns = parts[1].split(",");
            dependencies.add(new PrimaryKeyDependency(parts[0], Arrays.asList(columns)));
        }
        for (String fk : fks) {
            fk = fk.toUpperCase();
            String[] parts = fk.split(":", 2);
            String[] from = parts[0].split("\\.", 2);
            String[] to = parts[1].split("\\.", 2);
            dependencies.add(new ForeignKeyDependency(from[0], from[1], to[0], to[1]));
        }

        for (String dep : deps) {
            dependencies.add(new ImportedDependency(dep, rawSchema, parser));
        }

        this.schema = new Schema(context, relations, dependencies);
        List<Query> policyQueries = policySet.stream().map(p -> p.getSolverQuery(schema)).collect(Collectors.toList());
        this.determinacyFormula = new BasicDeterminacyFormula(schema, policyQueries);
        this.fastCheckDeterminacyFormula = new FastCheckDeterminacyFormula(schema, policyQueries);
        this.boundedDeterminacyFormula = new BoundedDeterminacyFormula(schema, policyQueries);
        this.unsatCoreDeterminacyFormula = new UnsatCoreDeterminacyFormula(schema, policySet, policyQueries, UNNAMED_EQUALITY, false);
        this.unsatCoreDeterminacyFormulaEliminate = new UnsatCoreDeterminacyFormula(schema, policySet, policyQueries, UNNAMED_EQUALITY, true);

        // Find an existing cache corresponding to `info`, or create a new one if one doesn't exist already.
        this.cache = decisionCaches.computeIfAbsent(info, (Properties _info) -> new DecisionCache(schema, policySet));
    }

    private boolean precheckPolicyApproval(PrivacyQuery query) {
        List<String> projectColumns = query.getProjectColumns();
        List<String> thetaColumns = query.getThetaColumns();
        projectColumns.addAll(thetaColumns);

        for (Set<String> s : cache.preapprovedSets) {
            if (s.containsAll(projectColumns)) {
                return true;
            }
        }
        return false;
    }

    private boolean precheckPolicyDenial(PrivacyQuery query, Policy policy) {
        return !policy.checkApplicable(new HashSet<>(query.getProjectColumns()), new HashSet<>(query.getThetaColumns()));
    }

    private void runExecutors(List<SMTExecutor> executors, CountDownLatch latch) {
        for (SMTExecutor executor : executors) {
            executor.start();
        }

        try {
            latch.await(SOLVE_TIMEOUT, TimeUnit.MILLISECONDS);
            for (SMTExecutor executor : executors) {
                executor.signalShutdown();
            }
            for (SMTExecutor executor : executors) {
                executor.join();
            }
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    private boolean doCheckPolicy(QueryTrace queries) {
        CountDownLatch latch = new CountDownLatch(1);
        List<SMTExecutor> executors = new ArrayList<>();

        // fast check
        long startTime = System.currentTimeMillis();
        String fastCheckSMT = this.fastCheckDeterminacyFormula.generateSMT(queries);
        System.out.println("\t| Make fastSMT:\t" + (System.currentTimeMillis() - startTime));
        executors.add(new Z3Executor(fastCheckSMT, latch, false, true, "z3_fast"));
        executors.add(new VampireLrsExecutor(fastCheckSMT, latch, false, true, "vampire_lrs_fast"));
//        executors.add(new VampireOttExecutor(fastCheckSMT, latch, false, true, "vampire_ott_fast"));
//        executors.add(new VampireDisExecutor(fastCheckSMT, latch, false, true, "vampire_dis_fast"));

        if (PRINT_FORMULAS) {
            try {
                Files.write(Paths.get(FORMULA_DIR + "/fast_unsat_" + queries.size() + ".smt2"),
                        fastCheckSMT.getBytes());
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }

        // regular check
        startTime = System.currentTimeMillis();
        String regularSMT = this.determinacyFormula.generateSMT(queries);
        System.out.println("\t| Make regular:\t" + (System.currentTimeMillis() - startTime));
//        executors.add(new Z3Executor(regularSMT, latch, true, true));
//        executors.add(new VampireCascExecutor(regularSMT, latch, true, true));
//        executors.add(new VampireFMBExecutor(regularSMT, latch, true, true));
        executors.add(new CVC4Executor(regularSMT, latch, true, true, "cvc4"));

        if (PRINT_FORMULAS) {
            try {
                Files.write(Paths.get(FORMULA_DIR + "/regular_" + queries.size() + ".smt2"),
                        regularSMT.getBytes());
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }

        // bounded check
        startTime = System.currentTimeMillis();
        String boundedSMT = this.boundedDeterminacyFormula.generateSMT(queries);
        System.out.println("\t| Make bounded:\t" + (System.currentTimeMillis() - startTime));
        executors.add(new Z3Executor(boundedSMT, latch, true, false, "z3_bounded"));

        if (PRINT_FORMULAS) {
            try {
                Files.write(Paths.get(FORMULA_DIR + "/bounded_" + queries.size() + ".smt2"),
                        boundedSMT.getBytes());
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }

        startTime = System.currentTimeMillis();
        runExecutors(executors, latch);
        final long solverDuration = System.currentTimeMillis() - startTime;

        for (SMTExecutor executor : executors) {
            if (executor.getResult() != Status.UNKNOWN) {
                String winner = executor.getName();
                System.out.println("\t| Invoke solvers:\t" + solverDuration + "," + winner);
                return executor.getResult() == Status.UNSATISFIABLE;
            }
        }

        System.err.println("timeout");
        // all timeout/inconclusive
        return false;
    }

    private static class UnsatCore {
        private final Set<String> core;
        private final Map<Object, Integer> equalityMap;

        public UnsatCore(Set<String> core, Map<Object, Integer> equalityMap) {
            this.core = core;
            this.equalityMap = equalityMap;
        }
    }

    private UnsatCore tryGetUnsatCore(QueryTrace queries) {
        CountDownLatch latch = new CountDownLatch(2);
        List<SMTExecutor> executors = new ArrayList<>();

        String smt = this.unsatCoreDeterminacyFormula.generateSMT(queries);
        Map<Object, Integer> equalityMap = this.unsatCoreDeterminacyFormula.getAssertionMap();
        executors.add(new CVC4Executor(smt, latch));
        if (PRINT_FORMULAS) {
            try {
                PrintWriter pw = new PrintWriter(FORMULA_DIR + "/gen_" + queries.size() + ".smt2");
                pw.println("(set-option :produce-unsat-cores true)");
                pw.println(smt);
                pw.println("(check-sat)(get-unsat-core)");
                pw.close();
            } catch (Exception e) {
                throw new RuntimeException(e);
                // do nothing
            }
        }

        smt = this.unsatCoreDeterminacyFormulaEliminate.generateSMT(queries);
        Map<Object, Integer> equalityMapEliminate = this.unsatCoreDeterminacyFormulaEliminate.getAssertionMap();
        executors.add(new CVC4Executor(smt, latch));
        if (PRINT_FORMULAS) {
            try {
                PrintWriter pw = new PrintWriter(FORMULA_DIR + "/gen_elim_" + queries.size() + ".smt2");
                pw.println("(set-option :produce-unsat-cores true)");
                pw.println(smt);
                pw.println("(check-sat)(get-unsat-core)");
                pw.close();
            } catch (Exception e) {
                throw new RuntimeException(e);
                // do nothing
            }
        }

        runExecutors(executors, latch);

        String[] minCore = null;
        Map<Object, Integer> usedEqualityMap = null;
        for (int i = 0; i < executors.size(); ++i) {
            SMTExecutor executor = executors.get(i);
            String[] core = executor.getUnsatCore();
            if (core != null) {
                System.err.println(Arrays.asList(core));
            } else {
                System.err.println("no result");
            }
            if (core != null && (minCore == null || minCore.length >= core.length)) {
                minCore = core;
                usedEqualityMap = (i < 1 ? equalityMap : equalityMapEliminate);
//                usedEqualityMap = equalityMapEliminate;
            }
        }

        return minCore == null ? null : new UnsatCore(new HashSet<>(Arrays.asList(minCore)), usedEqualityMap);
    }

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

    public boolean checkPolicy(QueryTrace queries) {
        PrivacyQuery currQuery = queries.getCurrentQuery().getQuery();
        System.out.println("transformed: "
                + currQuery.parsedSql.getParsedSql()
                + "\t" + currQuery.parameters);
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
        // todo: should we be caching timeout/unknown?
        boolean policyResult = doCheckPolicy(queries);
        if (ENABLE_CACHING) {
            cacheDecision(queries, policyResult);
        }
        return policyResult;
    }

    private void cacheDecision(QueryTrace queries, boolean policyResult) {
        UnsatCore core = null;
        if (policyResult) {
            core = tryGetUnsatCore(queries);
        }
        System.err.println("policy compliance: " + policyResult);
        if (core != null) {
            System.err.println("min core: " + core.core);
            CachedQueryTrace cacheTrace = new CachedQueryTrace();
            int queryNumber = 0;
            Set<Object> valueConstraints = new HashSet<>();
            Set<Integer> paramAssertions = new HashSet<>();
            Map<Integer, Integer> assertionOccurrences  = new HashMap<>();
            // check used values, assertions
            for (QueryTraceEntry queryEntry : queries.getAllEntries()) {
                boolean keptQuery = core.core.contains("a_q!" + queryNumber) || queryEntry == queries.getCurrentQuery();
                List<Object> parameters = queryEntry.getParameters();
                for (int i = 0; i < parameters.size(); ++i) {
                    Object parameter = parameters.get(i);
                    if (core.core.contains("a_pv!" + queryNumber + "!" + i)) {
                        valueConstraints.add(parameter);
                    }
                    if (!keptQuery || !core.equalityMap.containsKey(parameter)) {
                        continue;
                    }
                    int assertionNum = core.equalityMap.get(parameter);
                    if (UNNAMED_EQUALITY || core.core.contains("a_e!" + assertionNum)) {
                        paramAssertions.add(assertionNum);
                        assertionOccurrences.put(assertionNum, assertionOccurrences.getOrDefault(assertionNum, 0) + 1);
                    }
                }

                int attrNum = 0;
                for (List<Object> tuple : queryEntry.getTuples()) {
                    for (Object value : tuple) {
                        if (core.core.contains("a_v!" + queryNumber + "!" + attrNum)) {
                            valueConstraints.add(value);
                        }
                        if (!keptQuery || !core.equalityMap.containsKey(value)) {
                            ++attrNum;
                            continue;
                        }
                        int assertionNum = core.equalityMap.get(value);
                        if (UNNAMED_EQUALITY || core.core.contains("a_e!" + assertionNum)) {
                            assertionOccurrences.put(assertionNum, assertionOccurrences.getOrDefault(assertionNum, 0) + 1);
                        }
                        ++attrNum;
                    }
                }
                ++queryNumber;
            }
            queryNumber = 0;
            // generate cache entry
            for (QueryTraceEntry queryEntry : queries.getAllEntries()) {
                if (!core.core.contains("a_q!" + queryNumber) && queryEntry != queries.getCurrentQuery()) {
                    ++queryNumber;
                    continue;
                }
                // equalities
                List<CachedQueryTraceEntry.Index> parameterEquality = new ArrayList<>();
                for (Object parameter : queryEntry.getParameters()) {
                    if (!core.equalityMap.containsKey(parameter)) {
                        parameterEquality.add(null);
                        continue;
                    }
                    int assertionNum = core.equalityMap.get(parameter);
                    if (paramAssertions.contains(assertionNum) && assertionOccurrences.getOrDefault(assertionNum, 0) > 1) {
                        parameterEquality.add(new CachedQueryTraceEntry.Index(assertionNum));
                    } else {
                        parameterEquality.add(null);
                    }
                }
                List<List<CachedQueryTraceEntry.Index>> tupleEquality = new ArrayList<>();
                for (List<Object> tuple : queryEntry.getTuples()) {
                    List<CachedQueryTraceEntry.Index> indices = new ArrayList<>();
                    for (Object value : tuple) {
                        if (!core.equalityMap.containsKey(value)) {
                            indices.add(null);
                            continue;
                        }
                        int assertionNum = core.equalityMap.get(value);
                        if (paramAssertions.contains(assertionNum) && assertionOccurrences.getOrDefault(assertionNum, 0) > 1) {
                            indices.add(new CachedQueryTraceEntry.Index(assertionNum));
                        } else {
                            indices.add(null);
                        }
                    }
                    tupleEquality.add(indices);
                }
                // values
                QueryTraceEntry processedQuery = new QueryTraceEntry(queryEntry);
                List<Object> parameters = processedQuery.getParameters();
                for (int i = 0; i < parameters.size(); ++i) {
                    if (!valueConstraints.contains(parameters.get(i))) {
                        parameters.set(i, null);
                    }
                }
                for (List<Object> tuple : processedQuery.getTuples()) {
                    for (int j = 0; j < tuple.size(); ++j) {
                        if (!valueConstraints.contains(tuple.get(j))) {
                            tuple.set(j, null);
                        }
                    }
                }
                CachedQueryTraceEntry entry = new CachedQueryTraceEntry(processedQuery, queryEntry == queries.getCurrentQuery(), parameterEquality, tupleEquality);
                if (!entry.isEmpty()) {
                    cacheTrace.addEntry(entry);
                }
                ++queryNumber;
            }
            System.err.println(cacheTrace);
            cache.policyDecisionCacheFine.addToCache(queries.getCurrentQuery().getQuery().parsedSql.getParsedSql(), cacheTrace, policyResult);
        } else {
            System.err.println("no core, using value match");
            // no unsat core found (or not unsat) - all queries all values no equality
            CachedQueryTrace cacheTrace = new CachedQueryTrace();
            for (QueryTraceEntry queryEntry : queries.getAllEntries()) {
                List<CachedQueryTraceEntry.Index> parameterEquality = new ArrayList<>();
                for (int i = 0; i < queryEntry.getParameters().size(); ++i) {
                    parameterEquality.add(null);
                }
                List<List<CachedQueryTraceEntry.Index>> tupleEquality = new ArrayList<>();
                for (List<Object> queryEntryTuple : queryEntry.getTuples()) {
                    List<CachedQueryTraceEntry.Index> tuple = new ArrayList<>();
                    for (int j = 0; j < queryEntryTuple.size(); ++j) {
                        tuple.add(null);
                    }
                    tupleEquality.add(tuple);
                }
                cacheTrace.addEntry(new CachedQueryTraceEntry(queryEntry, queryEntry == queries.getCurrentQuery(), parameterEquality, tupleEquality));
            }
            System.err.println(cacheTrace);
            cache.policyDecisionCacheFine.addToCache(queries.getCurrentQuery().getQuery().parsedSql.getParsedSql(), cacheTrace, policyResult);
        }
    }

    // The fields of `DecisionCache` are shared between `QueryChecker` objects for the same database & policy.
    private static class DecisionCache {
        final ImmutableList<ImmutableSet<String>> preapprovedSets;
        final TraceCache policyDecisionCacheFine;

        public DecisionCache(Schema schema, ArrayList<Policy> policySet) {
            switch (PRECHECK_SETTING) {
                case DISABLED:
                    this.preapprovedSets = null;
                    break;
                case COARSE:
                    this.preapprovedSets = buildPreapprovedSetsCoarse(policySet);
                    break;
                case FULL:
                    this.preapprovedSets = buildPreapprovedSetsFull(schema, policySet);
                    break;
                default:
                    throw new IllegalStateException("invalid precheck setting: " + PRECHECK_SETTING);
            }
            this.policyDecisionCacheFine = new TraceCache();
        }

        /**
         * Returns the projected columns of each policy that has no `WHERE` clause.
         * @param policySet the set of policies from which to build the preapproved set.
         * @return the preapproved set.
         */
        private static ImmutableList<ImmutableSet<String>> buildPreapprovedSetsCoarse(ArrayList<Policy> policySet) {
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
