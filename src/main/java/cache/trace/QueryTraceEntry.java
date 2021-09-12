package cache.trace;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
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

    private List<Integer> pkValuedColIndices = null;

    private boolean computedColIndicesForPruning = false;
    private Collection<Integer> colIndicesForPruning = null;

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

    // Can only be called if tuples are returned.
    public List<Integer> getPkValuedColIndices(Schema schema) {
        if (pkValuedColIndices == null) {
            PrivacyQuery q = getQuery();
            checkState(hasTuples());
            int numColumns = getTuples().get(0).size();

            pkValuedColIndices = new ArrayList<>();
            ImmutableSet<String> pkValuedColumns = schema.getRawSchema().getPkValuedColumns();
            for (int colIdx = 0; colIdx < numColumns; ++colIdx) {
                for (String col : q.getNormalizedProjectColumnsByIdx(colIdx)) {
                    if (pkValuedColumns.contains(col)) {
                        pkValuedColIndices.add(colIdx);
                        break;
                    }
                }
            }
        }
        return pkValuedColIndices;
    }

    // Assumes that PK columns are integer.
    public Set<Integer> getReturnedPkValues(Schema schema) {
        if (!hasTuples()) {
            return Collections.emptySet();
        }
        Set<Integer> res = new HashSet<>();
        for (List<Object> tup : getTuples()) {
            for (Integer colIdx : getPkValuedColIndices(schema)) {
                res.add((Integer) tup.get(colIdx));
            }
        }
        return res;
    }

    public Optional<Collection<Integer>> isEligibleForPruning(Schema schema) {
        if (computedColIndicesForPruning) {
            return Optional.ofNullable(colIndicesForPruning);
        }

        computedColIndicesForPruning = true;
        List<List<Object>> tuples = getTuples();
        if (tuples.size() <= 3) { // Don't prune unless many rows are returned.
            colIndicesForPruning = null;
            return Optional.empty();
        }

        PrivacyQuery q = getQuery();
        int numColumns = getTuples().get(0).size();

        List<Integer> pkValuedColIndices = getPkValuedColIndices(schema);
        for (Iterator<Integer> it = pkValuedColIndices.iterator(); it.hasNext(); ) {
            int colIdx = it.next();
            Set<Object> values = tuples.stream().map(t -> t.get(colIdx)).collect(Collectors.toSet());
            if (values.size() == 1) {
                Object v = Iterables.getOnlyElement(values);
                if (q.parameters.contains(v)) {
                    it.remove();
                }
            }
        }

        if (pkValuedColIndices.isEmpty()) {
            colIndicesForPruning = null; // need at least one column for pruning.
        } else {
            colIndicesForPruning = pkValuedColIndices;
        }
        System.out.println("FOR PRUNE:\t" + getParsedSql());
        System.out.println("\t" + colIndicesForPruning);
        return Optional.ofNullable(colIndicesForPruning);
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
