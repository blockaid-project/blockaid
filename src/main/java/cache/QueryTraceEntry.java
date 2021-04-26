package cache;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class QueryTraceEntry {
    String queryText;
    List<Object> parameters;
    List<List<Object>> tuples;
    Map<String, Object> variables;

    public QueryTraceEntry(String queryText, List<Object> parameters, Map<String, Object> variables) {
        this(queryText, parameters, variables, new ArrayList<>());
    }

    public QueryTraceEntry(QueryTraceEntry entry, List<List<Object>> tuples) {
        this(entry.queryText, entry.parameters, entry.variables, tuples);
    }

    private QueryTraceEntry(String queryText, List<Object> parameters, Map<String, Object> variables, List<List<Object>> tuples) {
        this.queryText = queryText;
        this.parameters = parameters;
        this.variables = variables;
        this.tuples = tuples;
    }
}
