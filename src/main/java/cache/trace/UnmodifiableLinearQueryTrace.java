package cache.trace;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.ListMultimap;
import solver.Schema;
import sql.PrivacyQuery;
import sql.PrivacyQuerySelect;
import sql.SchemaPlusWithKey;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;

public abstract class UnmodifiableLinearQueryTrace {
    public abstract Map<String, Object> getConstMap();
    public abstract List<QueryTraceEntry> getAllEntries();
    public abstract QueryTraceEntry getCurrentQuery();

    public ListMultimap<String, Map<String, Object>> computeKnownRows(Schema schema) {
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
        for (QueryTraceEntry qte : getAllEntries()) {
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
                    // A SQL query can select the same pk column twice...
//                    checkState(!tableName2PkIdx.containsKey(tableName),
//                            "table already appeared: " + tableName);
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
}
