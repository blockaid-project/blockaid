package cache;

import sql.PrivacyQuery;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class QueryTrace {
    // order of past queries is irrelevant, so using a map for cache lookup
    Map<String, List<QueryTraceEntry>> queries = new HashMap<>();
    QueryTraceEntry currentQuery = null;
    private int sz = 0;

    public void startQuery(PrivacyQuery query, List<Object> parameters, Map<String, Integer> variableIndex) {
        assert currentQuery == null;
        Map<String, Object> variables = new HashMap<>();
        for (Map.Entry<String, Integer> index : variableIndex.entrySet()) {
            variables.put(index.getKey(), parameters.get(index.getValue()));
        }
        currentQuery = new QueryTraceEntry(query, parameters, variables);
        queries.putIfAbsent(query.parsedSql.getParsedSql(), new ArrayList<>());
        queries.get(query.parsedSql.getParsedSql()).add(currentQuery);

        ++sz;
    }

    public void endQuery(List<List<Object>> tuples) {
        assert currentQuery != null;
        queries.get(currentQuery.query.parsedSql.getParsedSql()).set(queries.get(currentQuery.query.parsedSql.getParsedSql()).size() - 1, new QueryTraceEntry(currentQuery, tuples));
        currentQuery = null;
    }

    public Map<String, List<QueryTraceEntry>> getQueries() {
        return queries;
    }

    public QueryTraceEntry getCurrentQuery() {
        return currentQuery;
    }

    public int size() {
        return sz;
    }
}
