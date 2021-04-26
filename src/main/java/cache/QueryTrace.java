package cache;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class QueryTrace {
    // order of past queries is irrelevant, so using a map for cache lookup
    Map<String, List<QueryTraceEntry>> queries = new HashMap<>();
    QueryTraceEntry currentQuery = null;

    public void startQuery(String queryText, List<Object> parameters, Map<String, Integer> variableIndex) {
        assert currentQuery == null;
        Map<String, Object> variables = new HashMap<>();
        for (Map.Entry<String, Integer> index : variableIndex.entrySet()) {
            variables.put(index.getKey(), parameters.get(index.getValue()));
        }
        currentQuery = new QueryTraceEntry(queryText, parameters, variables);
        queries.putIfAbsent(queryText, new ArrayList<>());
        queries.get(queryText).add(currentQuery);
    }

    public void endQuery(List<List<Object>> tuples) {
        assert currentQuery != null;
        queries.get(currentQuery.queryText).set(queries.get(currentQuery.queryText).size() - 1, new QueryTraceEntry(currentQuery, tuples));
        currentQuery = null;
    }
}
