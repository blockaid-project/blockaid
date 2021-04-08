package policy_checker;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.microsoft.z3.*;
import org.apache.calcite.schema.SchemaPlus;
import planner.PrivacyColumn;
import planner.PrivacyTable;
import solver.*;
import sql.PrivacyQuery;
import sql.QuerySequence;

import java.sql.Types;
import java.util.*;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

public class QueryChecker {
    private enum FastCheckDecision {
        ALLOW,
        DENY,
        UNKNOWN
    }

    private static long SOLVE_TIMEOUT = 15000; // ms

    private ArrayList<Policy> policySet;
    private List<Set<String>> preapprovedSets;
    private LoadingCache<PrivacyQueryCoarseWrapper, FastCheckDecision> policyDecisionCacheCoarse;
    private LoadingCache<QuerySequence, Boolean> policyDecisionCacheFine;
    private Context regularContext;
    private Context fastContext;
    private Schema regularSchema;
    private Schema fastSchema;
    private DeterminacyFormula fastCheckDeterminacyFormula;
    private DeterminacyFormula determinacyFormula;

    private static final int PREAPPROVE_MAX_PASSES = Integer.MAX_VALUE;

    // TODO read pk/fk from schema instead
    public QueryChecker(ArrayList<Policy> policySet, SchemaPlus rawSchema, String[] deps, String[] pks, String[] fks)
    {
        this.policySet = policySet;
        this.policyDecisionCacheCoarse = CacheBuilder.newBuilder()
                .build(new CacheLoader<PrivacyQueryCoarseWrapper, FastCheckDecision>() {
                    @Override
                    public FastCheckDecision load(final PrivacyQueryCoarseWrapper query) {
                        return doPrecheckPolicy(query.privacyQuery);
                    }
                });

        this.policyDecisionCacheFine = CacheBuilder.newBuilder()
                .build(new CacheLoader<QuerySequence, Boolean>() {
                    @Override
                    public Boolean load(final QuerySequence query) {
                        return doCheckPolicy(query);
                    }
                });

        this.regularContext = new Context();
        this.fastContext = new Context();

        this.preapprovedSets = new ArrayList<>();
        //buildPreapprovedSets();

        Map<String, List<Column>> relations = new HashMap<>();
        for (String tableName : rawSchema.getTableNames()) {
            PrivacyTable table = (PrivacyTable) rawSchema.getTable(tableName);
            List<Column> columns = new ArrayList<>();
            for (PrivacyColumn column : table.getColumns()) {
                Sort type;
                // TODO cleaner (??)
                // TODO(zhangwen): This really needs to be merged with the `fastSchema` creation logic.
                switch (column.type) {
                    case Types.INTEGER:
                    case Types.BIGINT:
                    case Types.TINYINT:
                        // TODO(zhangwen): Rails seems to use `tinyint(1)` for booleans.  Do we care?
                        type = regularContext.getIntSort();
                        break;
                    case Types.DOUBLE:
                        type = regularContext.getRealSort();
                        break;
                    case Types.BOOLEAN:
                        type = regularContext.getBoolSort();
                        break;
                    case Types.VARCHAR:
                    case Types.LONGVARCHAR:
                    case Types.CLOB:
                        type = regularContext.getStringSort();
                        break;
                    case Types.TIMESTAMP: // TODO
                    case Types.DATE:
                        type = regularContext.getStringSort();
                        break;
                    default:
                        throw new UnsupportedOperationException("bad column type: " + column.type + " for column " + tableName + "." + column.name);
                }
                // TODO(zhangwen): Other parts of the code seem to assume upper case table and column names (see
                //  ParsedPSJ.quantifyName), and so we upper case the column and table names here.  I hope this works.
                columns.add(new Column(column.name.toUpperCase(), type, null));
            }
            relations.put(tableName.toUpperCase(), columns);
        }

        List<Dependency> dependencies = new ArrayList<>();
        for (String pk : pks) {
            pk = pk.toUpperCase();
            String[] parts = pk.split(":", 2);
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

        this.regularSchema = new Schema(relations, dependencies);
        List<Query> policyQueries = policySet.stream().map(p -> p.getSolverQuery(regularSchema)).collect(Collectors.toList());
        this.determinacyFormula = new BasicDeterminacyFormula(regularContext, regularSchema, policyQueries);

        relations = new HashMap<>();
        for (String tableName : rawSchema.getTableNames()) {
            PrivacyTable table = (PrivacyTable) rawSchema.getTable(tableName);
            List<Column> columns = new ArrayList<>();
            for (PrivacyColumn column : table.getColumns()) {
                Sort type;
                switch (column.type) {
                    case Types.INTEGER:
                    case Types.BIGINT:
                    case Types.TINYINT:
                        // TODO(zhangwen): Rails seems to use `tinyint(1)` for booleans.  Do we care?
                        type = fastContext.getIntSort();
                        break;
                    case Types.DOUBLE:
                        type = fastContext.getRealSort();
                        break;
                    case Types.BOOLEAN:
                        type = fastContext.getBoolSort();
                        break;
                    case Types.VARCHAR:
                    case Types.LONGVARCHAR:
                    case Types.CLOB:
                        type = fastContext.getStringSort();
                        break;
                    case Types.TIMESTAMP: // TODO
                    case Types.DATE:
                        type = fastContext.getStringSort(); // datetime.. not really accurate
                        break;
                    default:
                        throw new UnsupportedOperationException("bad column type: " + column.type + " for column " + tableName + "." + column.name);
                }
                // TODO(zhangwen): Other parts of the code seem to assume upper case table and column names (see
                //  ParsedPSJ.quantifyName), and so we upper case the column and table names here.  I hope this works.
                columns.add(new Column(column.name.toUpperCase(), type, null));
            }
            relations.put(tableName.toUpperCase(), columns);
        }

        dependencies = new ArrayList<>();
        for (String pk : pks) {
            pk = pk.toUpperCase();
            String[] parts = pk.split(":", 2);
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

        this.fastSchema = new Schema(relations, dependencies);
        policyQueries = policySet.stream().map(p -> p.getSolverQuery(fastSchema)).collect(Collectors.toList());
        this.fastCheckDeterminacyFormula = new FastCheckDeterminacyFormula(fastContext, fastSchema, policyQueries);
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
        previousPass.put(Collections.emptySet(), new Entry(regularContext.mkBool(false), getAllColumns()));

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
                            BoolExpr nextPredicate = regularContext.mkOr(prevPredicate, policySet.get(j).getPredicate(regularContext));

                            Solver solver = regularContext.mkSolver();
                            solver.add(regularContext.mkNot(nextPredicate));
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
//        Set<String> projectColumns = query.getProjectColumns();
//        for (Set<String> s : preapprovedSets) {
//            if (containsAll(s, projectColumns)) {
//                return true;
//            }
//        }
//        return false;
        return false;
    }

    private boolean precheckPolicyDenial(PrivacyQuery query, Policy policy) {
//        return !policy.checkApplicable(query.getProjectColumns(), query.getThetaColumns());
        return false;
    }

    private boolean doCheckPolicy(QuerySequence queries) {
        CountDownLatch latch = new CountDownLatch(1);
        PrivacyQuery query = queries.get(queries.size() - 1).query;

        List<SMTExecutor> executors = new ArrayList<>();

//        long startTime = System.nanoTime();

        // fast check
        {
            Solver solver;
            {
                final long startTime = System.currentTimeMillis();
                solver = fastContext.mkSolver();
                solver.add(this.fastCheckDeterminacyFormula.makeFormula(queries));
                final long endTime = System.currentTimeMillis();
                System.out.println("\t| Make fast formula:\t" + (endTime - startTime));
            }

            {
                final long startTime = System.currentTimeMillis();
                Status res = solver.check();
                final long endTime = System.currentTimeMillis();
                System.out.println("\t| check:\t" + (endTime - startTime) + ", " + res);
            }

            String s;
            {
                final long startTime = System.currentTimeMillis();
                s = solver.toString();
                final long endTime = System.currentTimeMillis();
                System.out.println("\t| Formula toString:\t" + (endTime - startTime));
            }

            executors.add(new Z3Executor(s, latch, false, true));

//            try {
//                FileWriter writer = new FileWriter("/tmp/fast_check.smt2");
//                writer.append(s);
//                writer.flush();
//                writer.close();
//            } catch (IOException exp) {
//                System.err.println(exp.getMessage());
//            }
        }

        // regular check
        {
            final long startTime = System.currentTimeMillis();
            Solver solver = regularContext.mkSolver();
            solver.add(this.determinacyFormula.makeFormula(queries));
            String s = solver.toString();
            final long endTime = System.currentTimeMillis();
            System.out.println("\t| Make regular formula:\t" + (endTime - startTime));
            executors.add(new Z3Executor(s, latch, true, true));
//        executors.add(new VampireCascExecutor(s, latch, true, true));
//        executors.add(new VampireFMBExecutor(s, latch, true, true));
//        executors.add(new CVC4Executor(s, latch, true, true));
        }

        final long startTime = System.currentTimeMillis();
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
//        long endTime = System.nanoTime();
        final long endTime = System.currentTimeMillis();
        System.out.println("\t| Invoke solvers:\t" + (endTime - startTime));

//        System.err.println(((endTime - startTime) / 1000000000.0));
        for (SMTExecutor executor : executors) {
            if (executor.getResult() != Status.UNKNOWN) {
                return executor.getResult() == Status.UNSATISFIABLE;
            }
        }
        // all timeout/inconclusive
        return false;
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

    public boolean checkPolicy(QuerySequence queries) {
        try {
            FastCheckDecision precheckResult = policyDecisionCacheCoarse.get(new PrivacyQueryCoarseWrapper(queries.get(queries.size() - 1).query));
            if (precheckResult != FastCheckDecision.UNKNOWN) {
                return precheckResult == FastCheckDecision.ALLOW;
            }
            return policyDecisionCacheFine.get(queries.copy());
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
