package cache;

import sql.PrivacyQuery;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class QueryTraceEntry {
    PrivacyQuery query;
    List<Object> parameters;
    List<List<Object>> tuples;

    public QueryTraceEntry(PrivacyQuery query, List<Object> parameters) {
        this(query, parameters, new ArrayList<>());
    }

    public QueryTraceEntry(QueryTraceEntry entry, List<List<Object>> tuples) {
        this(entry.query, entry.parameters, tuples);
    }

    public QueryTraceEntry(QueryTraceEntry entry) {
        this(entry.query, entry.parameters, entry.tuples);
    }

    private QueryTraceEntry(PrivacyQuery query, List<Object> parameters, List<List<Object>> tuples) {
        this.query = query;
        this.parameters = new ArrayList<>(parameters);
        this.tuples = new ArrayList<>();
        for (List<Object> tuple : tuples) {
            this.tuples.add(new ArrayList<>(tuple));
        }
    }

    public PrivacyQuery getQuery() {
        return query;
    }

    public List<Object> getParameters() {
        return parameters;
    }

    public List<List<Object>> getTuples() {
        return tuples;
    }
}
