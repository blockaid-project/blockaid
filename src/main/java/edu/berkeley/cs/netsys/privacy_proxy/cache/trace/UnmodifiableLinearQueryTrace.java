package edu.berkeley.cs.netsys.privacy_proxy.cache.trace;

import com.google.common.collect.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Schema;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuerySelect;
import edu.berkeley.cs.netsys.privacy_proxy.sql.SchemaPlusWithKey;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public abstract class UnmodifiableLinearQueryTrace {
    public abstract Map<String, Object> getConstMap();
    public abstract List<QueryTraceEntry> getAllEntries(); // Includes current query.
    public abstract QueryTraceEntry getCurrentQuery();

    public int size() {
        return getAllEntries().size();
    }

    /**
     * Makes a sub-trace consisting of picked queries and tuples.  Always includes the current query, but does not put
     * it in the back map.
     * @param pickedQueryTuples picked (query index, tuple idx) pairs.
     * @return an unmodifiable linear sub-trace.
     */
    public SubQueryTrace getSubTrace(Collection<QueryTupleIdxPair> pickedQueryTuples) {
        // Maps query index to tuple indices.
        Multimap<Integer, Integer> picked = pickedQueryTuples.stream().collect(
                ImmutableSetMultimap.toImmutableSetMultimap(
                        QueryTupleIdxPair::queryIdx,
                        QueryTupleIdxPair::tupleIdx
                )
        );
        return getSubTrace(picked);
    }

    public SubQueryTrace getSubTrace(Multimap<Integer, Integer> pickedQueryTuples) {
        HashMap<QueryTupleIdxPair, QueryTupleIdxPair> backMap = new HashMap<>();
        ArrayList<QueryTraceEntry> newQueryList = new ArrayList<>();
        List<QueryTraceEntry> queryList = getAllEntries();
        for (int oldQueryIdx : pickedQueryTuples.keySet()) {
            QueryTraceEntry oldEntry = queryList.get(oldQueryIdx);

            List<List<Object>> oldTuples = oldEntry.getTuples();
            ArrayList<List<Object>> newTuples = new ArrayList<>();
            for (int oldTupleIdx : pickedQueryTuples.get(oldQueryIdx)) {
                backMap.put(
                        new QueryTupleIdxPair(newQueryList.size(), newTuples.size()),
                        new QueryTupleIdxPair(oldQueryIdx, oldTupleIdx)
                );
                newTuples.add(oldTuples.get(oldTupleIdx));
            }
            newQueryList.add(new QueryTraceEntry(oldEntry.getQuery(), oldEntry.getParameters(), newTuples));
        }

        QueryTraceEntry currQuery = getCurrentQuery();
        checkState(currQuery != null);
        checkArgument(!pickedQueryTuples.containsKey(queryList.size() - 1), "the current query cannot be picked");
        QueryTraceEntry newCurrQuery = new QueryTraceEntry(currQuery);
        newQueryList.add(newCurrQuery);
        return new SubQueryTrace(newQueryList, getConstMap(), newCurrQuery, backMap);
    }

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
            if (!(pq instanceof PrivacyQuerySelect pqs)) {
                continue;
            }

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

    private record TableColumnPair(String table, Object value) {}

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        List<QueryTraceEntry> allEntries = getAllEntries();
        for (int i = 0; i < allEntries.size(); ++i) {
            QueryTraceEntry qte = allEntries.get(i);
            boolean isCurrentQuery = qte == getCurrentQuery();
            if (isCurrentQuery) {
                sb.append("[*] ");
            } else {
                sb.append("[").append(i).append("] ");
            }
            sb.append(qte.getParsedSql()).append("\n");
            if (!isCurrentQuery) {
                sb.append("\t").append(qte.getTuples().size()).append(" tuple(s)\n");
            }
        }
        return sb.toString();
    }
}
