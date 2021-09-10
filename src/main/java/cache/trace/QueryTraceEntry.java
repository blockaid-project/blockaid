package cache.trace;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import solver.Schema;
import solver.Tuple;
import sql.PrivacyQuery;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public class QueryTraceEntry {
    private final PrivacyQuery query;
    private final List<Object> parameters;
    private ImmutableList<List<Object>> tuples; // Nullable.

    private Integer pkColIdxForCutting = null; // If ineligible, -1.  If not computed, null.

    public QueryTraceEntry(PrivacyQuery query, List<Object> parameters) {
        this(checkNotNull(query), checkNotNull(parameters), null);
    }

    public QueryTraceEntry(QueryTraceEntry entry) {
        this(entry.query, entry.parameters, entry.tuples);
    }

    QueryTraceEntry(PrivacyQuery query, List<Object> parameters, List<List<Object>> tuples) {
        this.query = query;
        this.parameters = new ArrayList<>(parameters);
        if (tuples == null) {
            this.tuples = null;
        } else {
            this.tuples = deepCopyTuples(tuples);
        }
    }

    private static ImmutableList<List<Object>> deepCopyTuples(List<List<Object>> tuples) {
        checkNotNull(tuples);
        return tuples.stream().map(ArrayList::new).collect(ImmutableList.toImmutableList());
    }

    public PrivacyQuery getQuery() {
        return query;
    }

    public String getParsedSql() {
        return query.parsedSql.getParsedSql();
    }

    /**
     * Sets the returned tuples of this query.  CAN ONLY be called if no tuples were previously recorded.
     * @param tuples returned tuples.
     */
    public void setTuples(List<List<Object>> tuples) {
        checkNotNull(tuples);
        checkState(this.tuples == null); // Ensure that no tuples were previously recorded.
        this.tuples = deepCopyTuples(tuples);
    }

    public List<Object> getParameters() {
        return parameters;
    }

    public List<List<Object>> getTuples() {
        if (tuples == null) {
            return Collections.emptyList();
        }
        return tuples;
    }

    public Stream<List<Object>> getTuplesStream() {
        if (tuples == null) {
            return Stream.empty();
        }
        return tuples.stream();
    }

    public boolean hasTuples() {
        // TODO(zhangwen): It's kind of weird to treat these two cases in the same way.
        return tuples != null && !tuples.isEmpty();
    }

    /**
     * Identifies whether this QTE qualifies for cutting and, if so, identifies PK column.
     * @param schema The schema.  TODO(zhangwen): should really be a member of this class.
     * @return If QTE qualifies for culling, the ID of column whose value to look for in the query being checked; empty
     * otherwise.
     */
    public Optional<Integer> isEligibleForCutting(Schema schema) {
        if (pkColIdxForCutting != null) {
            if (pkColIdxForCutting < 0) {
                return Optional.empty();
            }
            return Optional.of(pkColIdxForCutting);
        }

        pkColIdxForCutting = -1;

        List<List<Object>> tuples = getTuples();
        if (tuples.size() <= 3) {
            return Optional.empty();
        }

        // This query returned lots of tuples.  Cull some of them?
        PrivacyQuery q = getQuery();
        int numColumns = tuples.get(0).size();

        Integer pkColIdx = null;
        HashMap<String, String> colName2PkCol = new HashMap<>();
        for (int colIdx = 0; colIdx < numColumns; ++colIdx) {
            Set<String> projCols = q.getNormalizedProjectColumnsByIdx(colIdx);
            if (projCols.size() != 1) {
                // Not supported.
                return Optional.empty();
            }
            String[] parts = Iterables.getOnlyElement(projCols).split("\\.");
            String pkColName = colName2PkCol.computeIfAbsent(parts[0], tableName -> {
                Optional<ImmutableList<String>> oPkCols = schema.getRawSchema().getPrimaryKeyColumns(tableName);
                if (oPkCols.isEmpty()) {
                    return null;
                }
                ImmutableList<String> pkCols = oPkCols.get();
                if (pkCols.size() != 1) {
                    return null;
                }
                return pkCols.get(0);
            });
            if (pkColName == null) {
                return Optional.empty();
            }
            if (parts[1].equals(pkColName)) {
                if (pkColIdx == null) {
                    pkColIdx = colIdx;
                } else {
                    return Optional.empty(); // Multiple primary key columns selected? Not supported.
                }
            }
        }

        if (pkColIdx != null) {
            this.pkColIdxForCutting = pkColIdx;
        }
        return Optional.ofNullable(pkColIdx);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        QueryTraceEntry that = (QueryTraceEntry) o;
        return query.equals(that.query) && parameters.equals(that.parameters) && Objects.equals(tuples, that.tuples);
    }

    @Override
    public int hashCode() {
        return Objects.hash(query, parameters, tuples);
    }
}
