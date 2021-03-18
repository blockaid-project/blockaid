package sql;

import java.util.List;
import java.util.Objects;

public class QueryWithResult {
    public PrivacyQuery query;
    public List<List<Object>> tuples;

    public QueryWithResult(PrivacyQuery query) {
        this(query, null);
    }

    public QueryWithResult(PrivacyQuery query, List<List<Object>> tuples) {
        this.query = query;
        this.tuples = tuples;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        QueryWithResult that = (QueryWithResult) o;
        return Objects.equals(query, that.query) &&
                Objects.equals(tuples, that.tuples);
    }

    @Override
    public int hashCode() {
        return Objects.hash(query, tuples);
    }
}
