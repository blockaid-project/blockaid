package cache;

import com.google.common.collect.ImmutableList;
import sql.PrivacyQuery;

import java.util.*;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public class QueryTraceEntry {
    private final PrivacyQuery query;
    private final List<Object> parameters;
    private ImmutableList<List<Object>> tuples; // Nullable.

    public QueryTraceEntry(PrivacyQuery query, List<Object> parameters) {
        this(query, parameters, null);
    }

    public QueryTraceEntry(QueryTraceEntry entry) {
        this(entry.query, entry.parameters, entry.tuples);
    }

    private QueryTraceEntry(PrivacyQuery query, List<Object> parameters, List<List<Object>> tuples) {
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

    public Iterable<List<Object>> getTuples() {
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
}
