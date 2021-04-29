package policy_checker;

import cache.*;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.microsoft.z3.*;
import planner.PrivacyColumn;
import planner.PrivacyTable;
import solver.*;
import sql.PrivacyQuery;
import sql.SchemaPlusWithKey;

import java.util.*;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

public class QueryChecker {
    public static boolean ENABLE_CACHING = true;
    public static boolean ENABLE_PRECHECK = true;

    private enum FastCheckDecision {
        ALLOW,
        DENY,
        UNKNOWN
    }

    public static long SOLVE_TIMEOUT = 15000; // ms

    private ArrayList<Policy> policySet;
    private List<Set<String>> preapprovedSets;
    private LoadingCache<PrivacyQueryCoarseWrapper, FastCheckDecision> policyDecisionCacheCoarse;
    private TraceCache policyDecisionCacheFine;
    private Context context;
    private Schema schema;
    private DeterminacyFormula fastCheckDeterminacyFormula;
    private DeterminacyFormula determinacyFormula;
    private DeterminacyFormula unsatCoreDeterminacyFormula;

    private static final int PREAPPROVE_MAX_PASSES = Integer.MAX_VALUE;

    private static QueryChecker instance = null;

    public static QueryChecker getInstance(ArrayList<Policy> policySet, SchemaPlusWithKey rawSchema, String[] deps, String[] uks, String[] fks) {
        if (instance == null) {
            instance = new QueryChecker(policySet, rawSchema, deps, uks, fks);
        }
        return instance;
    }

    // TODO read pk/fk from schema instead
    private QueryChecker(ArrayList<Policy> policySet, SchemaPlusWithKey rawSchema, String[] deps, String[] uks, String[] fks)
    {
        this.policySet = policySet;
        this.policyDecisionCacheCoarse = CacheBuilder.newBuilder()
                .maximumSize(ENABLE_CACHING ? Integer.MAX_VALUE : 0)
                .build(new CacheLoader<PrivacyQueryCoarseWrapper, FastCheckDecision>() {
                    @Override
                    public FastCheckDecision load(final PrivacyQueryCoarseWrapper query) {
                        return doPrecheckPolicy(query.privacyQuery);
                    }
                });

        this.policyDecisionCacheFine = new TraceCache();

        this.context = new Context();

        Map<String, List<Column>> relations = new HashMap<>();
        for (String tableName : rawSchema.schema.getTableNames()) {
            PrivacyTable table = (PrivacyTable) rawSchema.schema.getTable(tableName);
            List<Column> columns = new ArrayList<>();
            for (PrivacyColumn column : table.getColumns()) {
                Sort type = Schema.getSortFromSqlType(context, column.type);
                columns.add(new Column(column.name, type, null));
            }
            relations.put(tableName, columns);
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
            dependencies.add(new ImportedDependency(dep));
        }

        this.schema = new Schema(relations, dependencies);
        List<Query> policyQueries = policySet.stream().map(p -> p.getSolverQuery(schema)).collect(Collectors.toList());
        this.determinacyFormula = new BasicDeterminacyFormula(context, schema, policyQueries);
        this.fastCheckDeterminacyFormula = new FastCheckDeterminacyFormula(context, schema, policyQueries);
        this.unsatCoreDeterminacyFormula = new UnsatCoreDeterminacyFormula(context, schema, policyQueries);

        if (ENABLE_PRECHECK) {
            this.preapprovedSets = new ArrayList<>();
            buildPreapprovedSets();
        }
    }

    private void buildPreapprovedSets() {
        class Entry {
            private BoolExpr predicate;
            private Set<String> columns;

            public Entry(BoolExpr predicate, Set<String> columns) {
                this.predicate = predicate;
                this.columns = columns;
            }
        }

        Map<Set<Integer>, Entry> previousPass = new HashMap<>();
        previousPass.put(Collections.emptySet(), new Entry(context.mkBool(false), getAllColumns()));

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
                        Set<String> nextColumns = setIntersection(prevColumns, policySet.get(j).getProjectColumns());

                        if (!nextColumns.isEmpty()) {
                            BoolExpr nextPredicate = context.mkOr(prevPredicate, policySet.get(j).getPredicate(context, schema));

                            Solver solver = context.mkSolver();
                            solver.add(context.mkNot(nextPredicate));
                            Status q = solver.check();
                            boolean predicateResult = (q == Status.UNSATISFIABLE);
                            currentPass.put(nextSet, new Entry(predicateResult ? null : nextPredicate, nextColumns));
                        }
                    }
                }
            }

            for (Set<Integer> s : remove) {
                currentPass.remove(s);
            }

            for (Map.Entry<Set<Integer>, Entry> entry : currentPass.entrySet()) {
                if (entry.getValue().predicate == null) {
                    preapprovedSets.add(entry.getValue().columns);
                }
            }

            previousPass = currentPass;
        }
    }

    private Set<String> getAllColumns() {
        Set<String> r = new HashSet<>();
        for (Policy policy : policySet) {
            r.addAll(policy.getProjectColumns());
        }
        return r;
    }

    private <T> Set<T> setIntersection(Set<T> s1, Set<T> s2) {
        Set<T> sr = new HashSet<>(s1);
        for (T x : s1) {
            if (!s2.contains(x)) {
                sr.remove(x);
            }
        }

        return sr;
    }

    private boolean containsAll(Collection<String> set, Collection<String> query) {
        return set.containsAll(query);
    }

    private boolean precheckPolicyApproval(PrivacyQuery query) {
        Set<String> projectColumns = query.getProjectColumns();
        Set<String> thetaColumns = query.getThetaColumns();
        projectColumns.addAll(thetaColumns);

        for (Set<String> s : preapprovedSets) {
            if (containsAll(s, projectColumns)) {
                return true;
            }
        }
        return false;
    }

    private boolean precheckPolicyDenial(PrivacyQuery query, Policy policy) {
        return !policy.checkApplicable(query.getProjectColumns(), query.getThetaColumns());
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

        String smt;
        // fast check
        smt = this.fastCheckDeterminacyFormula.generateSMT(queries);
        executors.add(new Z3Executor(smt, latch, false, true));

        // regular check
        smt = this.determinacyFormula.generateSMT(queries);
        executors.add(new Z3Executor(smt, latch, true, true));
        executors.add(new VampireCascExecutor(smt, latch, true, true));
        executors.add(new VampireFMBExecutor(smt, latch, true, true));
        executors.add(new CVC4Executor(smt, latch, true, true));

        runExecutors(executors, latch);

        for (SMTExecutor executor : executors) {
            if (executor.getResult() != Status.UNKNOWN) {
                return executor.getResult() == Status.UNSATISFIABLE;
            }
        }

        // all timeout/inconclusive
        return false;
    }

    private String[] tryGetUnsatCore(QueryTrace queries) {
        CountDownLatch latch = new CountDownLatch(2);
        List<SMTExecutor> executors = new ArrayList<>();

        String smt = this.unsatCoreDeterminacyFormula.generateSMT(queries);
        executors.add(new Z3Executor(smt, latch));
        executors.add(new CVC4Executor(smt, latch));

        runExecutors(executors, latch);

        String[] minCore = null;
        for (SMTExecutor executor : executors) {
            String[] core = executor.getUnsatCore();
            if (core != null && (minCore == null || minCore.length > core.length)) {
                minCore = core;
            }
        }

        return minCore;
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
        try {
            if (ENABLE_PRECHECK) {
                FastCheckDecision precheckResult = policyDecisionCacheCoarse.get(new PrivacyQueryCoarseWrapper(queries.getCurrentQuery().getQuery()));
                if (precheckResult == FastCheckDecision.ALLOW) {
                    return true;
                }
                if (precheckResult == FastCheckDecision.DENY && queries.size() == 1) {
                    // fast check deny will reject queries that depend on past data
                    return false;
                }
            }
            if (ENABLE_CACHING) {
                Boolean cacheResult = policyDecisionCacheFine.checkCache(queries);
                if (cacheResult != null) {
                    return cacheResult;
                }
            }
            // todo: should we be caching timeout/unknown?
            boolean policyResult = doCheckPolicy(queries);
            if (ENABLE_CACHING) {
                new Thread(() -> {
                    String[] minCore = null;
                    if (policyResult) {
                        minCore = tryGetUnsatCore(queries);
                    }
                    if (minCore != null) {
                        // System.err.println("min core: " + Arrays.asList(minCore));
                        CachedQueryTrace cacheTrace = new CachedQueryTrace();
                        int queryNumber = 0;
                        Set<String> core = new HashSet<>(Arrays.asList(minCore));
                        for (List<QueryTraceEntry> queryEntries : queries.getQueries().values()) {
                            for (QueryTraceEntry queryEntry : queryEntries) {
                                if (!core.contains("a_q!" + queryNumber) && queryEntry != queries.getCurrentQuery()) {
                                    ++queryNumber;
                                    continue;
                                }
                                // equalities
                                List<CachedQueryTraceEntry.Index> parameterEquality = new ArrayList<>();
                                for (int i = 0; i < queryEntry.getParameters().size(); ++i) {
                                    parameterEquality.add(null); // TODO
                                }
                                List<List<CachedQueryTraceEntry.Index>> tupleEquality = new ArrayList<>();
                                for (int i = 0; i < queryEntry.getTuples().size(); ++i) {
                                    List<CachedQueryTraceEntry.Index> tuple = new ArrayList<>();
                                    for (int j = 0; j < queryEntry.getTuples().get(i).size(); ++j) {
                                        tuple.add(null); // TODO
                                    }
                                    tupleEquality.add(tuple);
                                }
                                // values
                                QueryTraceEntry processedQuery = new QueryTraceEntry(queryEntry);
                                List<Object> parameters = processedQuery.getParameters();
                                for (int i = 0; i < parameters.size(); ++i) {
                                    if (!core.contains("a_pv!" + queryNumber + "!" + i)) {
                                        parameters.set(i, null);
                                    }
                                }

                                int attrNum = 0;
                                for (List<Object> tuple : processedQuery.getTuples()) {
                                    for (int j = 0; j < tuple.size(); ++j) {
                                        if (!core.contains("a_v!" + queryNumber + "!" + attrNum)) {
                                            tuple.set(j, null);
                                        }
                                        ++attrNum;
                                    }
                                }
                                cacheTrace.addEntry(new CachedQueryTraceEntry(processedQuery, parameterEquality, tupleEquality));
                                ++queryNumber;
                            }
                        }
                        policyDecisionCacheFine.addToCache(queries.getCurrentQuery().getQuery().parsedSql.getParsedSql(), cacheTrace, policyResult);
                    } else {
                        // System.err.println("no core, using value match");
                        // no unsat core found (or not unsat) - all queries all values no equality
                        CachedQueryTrace cacheTrace = new CachedQueryTrace();
                        for (List<QueryTraceEntry> queryEntries : queries.getQueries().values()) {
                            for (QueryTraceEntry queryEntry : queryEntries) {
                                List<CachedQueryTraceEntry.Index> parameterEquality = new ArrayList<>();
                                for (int i = 0; i < queryEntry.getParameters().size(); ++i) {
                                    parameterEquality.add(null);
                                }
                                List<List<CachedQueryTraceEntry.Index>> tupleEquality = new ArrayList<>();
                                for (int i = 0; i < queryEntry.getTuples().size(); ++i) {
                                    List<CachedQueryTraceEntry.Index> tuple = new ArrayList<>();
                                    for (int j = 0; j < queryEntry.getTuples().get(i).size(); ++j) {
                                        tuple.add(null);
                                    }
                                    tupleEquality.add(tuple);
                                }
                                cacheTrace.addEntry(new CachedQueryTraceEntry(queryEntry, parameterEquality, tupleEquality));
                            }
                        }
                        policyDecisionCacheFine.addToCache(queries.getCurrentQuery().getQuery().parsedSql.getParsedSql(), cacheTrace, policyResult);
                    }
                }).run();
            }
            return policyResult;
        } catch (ExecutionException e) {
            throw propagate(e);
        }
    }

    private RuntimeException propagate(Throwable e) {
        if (e instanceof RuntimeException) {
            throw (RuntimeException) e;
        } else if (e instanceof Error) {
            throw (Error) e;
        } else {
            throw new RuntimeException(e.getMessage());
        }
    }

    private static class PrivacyQueryCoarseWrapper {
        private PrivacyQuery privacyQuery;

        public PrivacyQueryCoarseWrapper(PrivacyQuery privacyQuery) {
            this.privacyQuery = privacyQuery;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            PrivacyQueryCoarseWrapper query = (PrivacyQueryCoarseWrapper) o;
            return privacyQuery.parsedSql.equals(query.privacyQuery.parsedSql);
        }

        @Override
        public int hashCode() {
            return Objects.hash(privacyQuery.parsedSql);
        }
    }
}
