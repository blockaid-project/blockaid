package cache;

import sql.PrivacyQuery;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class QueryTraceEntry {
    PrivacyQuery query;
    List<Object> parameters;
    List<List<Object>> tuples;
    Map<String, Object> variables;

    public QueryTraceEntry(PrivacyQuery query, List<Object> parameters, Map<String, Object> variables) {
        this(query, parameters, variables, new ArrayList<>());
    }

    public QueryTraceEntry(QueryTraceEntry entry, List<List<Object>> tuples) {
        this(entry.query, entry.parameters, entry.variables, tuples);
    }

    private QueryTraceEntry(PrivacyQuery query, List<Object> parameters, Map<String, Object> variables, List<List<Object>> tuples) {
        this.query = query;
        this.parameters = parameters;
        this.variables = variables;
        this.tuples = tuples;
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
