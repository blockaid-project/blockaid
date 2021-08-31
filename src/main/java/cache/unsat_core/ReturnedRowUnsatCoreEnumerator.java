package cache.unsat_core;

import cache.MyUnsatCoreDeterminacyFormula;
import cache.labels.ReturnedRowLabel;
import cache.trace.*;
import com.google.common.collect.*;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import solver.*;
import solver.executor.VampireCASCProofExecutor;
import sql.PrivacyQuery;
import sql.PrivacyQuerySelect;
import sql.SchemaPlusWithKey;

import java.util.*;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static util.TerminalColor.*;

public class ReturnedRowUnsatCoreEnumerator extends AbstractUnsatCoreEnumerator<ReturnedRowLabel>
        implements AutoCloseable {
    private final Schema schema;
    private final Collection<Query> views;
    private final QueryTrace trace;

    private Set<ReturnedRowLabel> prevCore = null;

    public static ReturnedRowUnsatCoreEnumerator create(Schema schema, Collection<Query> views, QueryTrace trace) {
        // TODO(zhangwen): This code is duplicated.
        ArrayList<ReturnedRowLabel> rrls = new ArrayList<>();
        int queryIdx = 0;
        for (QueryTraceEntry entry : trace.getAllEntries()) {
            for (int tupIdx = 0; tupIdx < entry.getTuples().size(); ++tupIdx) {
                rrls.add(new ReturnedRowLabel(queryIdx, tupIdx));
            }
            ++queryIdx;
        }
        return new ReturnedRowUnsatCoreEnumerator(schema, views, trace, rrls);
    }

    private ReturnedRowUnsatCoreEnumerator(Schema schema, Collection<Query> views, QueryTrace trace,
                                           Collection<ReturnedRowLabel> labels) {
        super(schema.getContext(), labels, Order.DECREASING);
        schema.getContext().startCachingConsts();
        this.schema = schema;
        this.views = views;
        this.trace = trace;
    }

    private Status solveWithVampire(Set<ReturnedRowLabel> labels) {
        MyZ3Context context = schema.getContext();
        Solver solver = context.mkSolver();
        MyUnsatCoreDeterminacyFormula myFormula = new MyUnsatCoreDeterminacyFormula(schema, views, trace);
        solver.add(Iterables.toArray(myFormula.makeBackgroundFormulas(), BoolExpr.class));

        Map<ReturnedRowLabel, BoolExpr> labeledExprs = myFormula.makeLabeledExprs();
        for (Map.Entry<ReturnedRowLabel, BoolExpr> entry : labeledExprs.entrySet()) {
            if (labels.contains(entry.getKey())) {
                solver.add(context.mkImplies(
                        context.mkBoolConst(entry.getKey().toString()),
                        entry.getValue()
                ));
            }
        }
        solver.push();
        for (ReturnedRowLabel l : labels) {
            solver.add(context.mkBoolConst(l.toString()));
        }
        String smt = solver.toString();
        solver.pop();

        VampireCASCProofExecutor executor = new VampireCASCProofExecutor("vampire", smt, null);
        String output = executor.doRunRaw();
//        System.out.println(output);
        if (output.contains("Termination reason: Satisfiable\n")) {
            return Status.SATISFIABLE;
        }

        if (output.contains("Termination reason: Refutation\n")) {
            // TODO(zhangwen): this is ugly.
            Set<ReturnedRowLabel> core = Pattern.compile("ReturnedRowLabel!(\\d+)!(\\d+)").matcher(output).results()
                    .map(r -> new ReturnedRowLabel(Integer.parseInt(r.group(1)), Integer.parseInt(r.group(2))))
                    .collect(Collectors.toSet());
            System.out.println(ANSI_RED + ANSI_BLUE_BACKGROUND + core + ANSI_RESET);

            this.prevCore = core;
            return Status.UNSATISFIABLE;
        }

        return Status.UNKNOWN;
    }

    @Override
    protected Optional<Set<ReturnedRowLabel>> getUnsatCore() {
        return Optional.ofNullable(this.prevCore);
    }

    @Override
    protected Optional<Set<ReturnedRowLabel>> isSubsetSat(Set<ReturnedRowLabel> labels) {
        this.prevCore = null;
        Status res = solveWithVampire(labels);
        if (res == Status.SATISFIABLE) {
            return Optional.of(labels);
        } else if (res == Status.UNSATISFIABLE) {
            return Optional.empty();
        }

        SubQueryTrace sqt = trace.getSubTrace(
                labels.stream()
                        .map(rrl -> new QueryTupleIdxPair(rrl.getQueryIdx(), rrl.getRowIdx()))
                        .collect(ImmutableList.toImmutableList())
        );

        BoundEstimator boundEstimator = new UnsatCoreBoundEstimator(new CountingBoundEstimator());
        Map<String, Integer> bounds = boundEstimator.calculateBounds(schema, sqt);
        Map<String, Integer> slackBounds = Maps.transformValues(bounds, n -> n + 2);

        BoundedDeterminacyFormula formula = new BoundedDeterminacyFormula(schema, views, slackBounds, true,
                DeterminacyFormula.TextOption.NO_TEXT, computeKnownRows(schema, sqt));
        Solver solver = schema.getContext().mkSolver();
        solver.add(Iterables.toArray(formula.makeCompleteFormula(sqt), BoolExpr.class));
        Status status = solver.check();
        checkState(status == Status.SATISFIABLE);
        return Optional.of(labels);
//        checkState(status == Status.UNSATISFIABLE, "solver returned: " + status);
//        System.out.println(ANSI_RED + labels.size() + "\t" + labels + ANSI_RESET);
//        this.prevLabels = ImmutableSet.copyOf(labels);
//        return Optional.empty();
    }

    @Override
    public void close() throws Exception {
        schema.getContext().stopCachingConsts();
    }

    private static class TableColumnPair {
        public final String table;
        public final Object value;

        public TableColumnPair(String table, Object value) {
            this.table = table;
            this.value = value;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            TableColumnPair that = (TableColumnPair) o;
            return table.equals(that.table) && value.equals(that.value);
        }

        @Override
        public int hashCode() {
            return Objects.hash(table, value);
        }
    }

    private static ListMultimap<String, Map<String, Object>> computeKnownRows(
            Schema schema, UnmodifiableLinearQueryTrace trace) {
        SchemaPlusWithKey rawSchema = schema.getRawSchema();
        Map<String, String> tableName2PkName = new HashMap<>();
        for (String tableName : schema.getRelationNames()) {
            Optional<ImmutableList<String>> oPkColumns = rawSchema.getPrimaryKeyColumns(tableName);
            if (oPkColumns.isEmpty()) {
                continue;
            }

            // Currently, only supports tables with exactly one primary key column.
            ImmutableList<String> pkColumns = oPkColumns.get();
            if (pkColumns.size() != 1) {
                continue;
            }
            tableName2PkName.put(tableName, Iterables.getOnlyElement(pkColumns));
        }

        Map<TableColumnPair, Map<String, Object>> tablePk2Rows = new HashMap<>();
        for (QueryTraceEntry qte : trace.getAllEntries()) {
            if (!qte.hasTuples()) {
                continue;
            }
            List<List<Object>> tuples = qte.getTuples();
            // TODO(zhangwen): add a method to query that returns the number of columns.
            int numColumns = tuples.get(0).size();

            PrivacyQuery pq = qte.getQuery();
            if (!(pq instanceof PrivacyQuerySelect)) {
                continue;
            }
            PrivacyQuerySelect pqs = (PrivacyQuerySelect) pq;

            // Maps table name to the column index of its primary key, if returned by the query.
            List<String[]> columns = new ArrayList<>();
            Map<String, Integer> tableName2PkIdx = new HashMap<>();
            for (int colIdx = 0; colIdx < numColumns; ++colIdx) {
                Set<String> columnNames = pqs.getProjectColumnsByIdx(colIdx);
                checkState(columnNames.size() == 1,
                        "a SELECT query should have exactly one column name per index, got: " + columnNames);
                String columnName = Iterables.getOnlyElement(columnNames);

                String[] parts = columnName.split("\\.", 2);
                String tableName = parts[0];
                // FIXME(zhangwen): assumes that no table is aliased to another table's name.
                if (parts[1].equals(tableName2PkName.get(tableName))) {
                    checkState(!tableName2PkIdx.containsKey(tableName));
                    tableName2PkIdx.put(tableName, colIdx);
                }

                columns.add(parts);
            }

            for (List<Object> tup : tuples) {
                Map<String, TableColumnPair> tableName2PkValue = new HashMap<>();
                for (Map.Entry<String, Integer> e : tableName2PkIdx.entrySet()) {
                    String tableName = e.getKey();
                    tableName2PkValue.put(tableName, new TableColumnPair(tableName, tup.get(e.getValue())));
                }

                for (int colIdx = 0; colIdx < tup.size(); ++colIdx) {
                    String[] parts = columns.get(colIdx);
                    Object pkValue = tableName2PkValue.get(parts[0]);
                    if (pkValue == null) {
                        continue;
                    }
                    TableColumnPair tcp = tableName2PkValue.get(parts[0]);
                    if (tcp == null) {
                        continue;
                    }
                    Map<String, Object> knownRow = tablePk2Rows.computeIfAbsent(tcp, k -> new HashMap<>());
                    if (knownRow.containsKey(parts[1])) {
                        checkState(Objects.equals(knownRow.get(parts[1]), tup.get(colIdx)));
                    } else {
                        knownRow.put(parts[1], tup.get(colIdx));
                    }
                }
            }
        }

        ListMultimap<String, Map<String, Object>> knownRows = ArrayListMultimap.create();
        for (Map.Entry<TableColumnPair, Map<String, Object>> e : tablePk2Rows.entrySet()) {
            knownRows.put(e.getKey().table, e.getValue());
        }
        return knownRows;
    }


}
