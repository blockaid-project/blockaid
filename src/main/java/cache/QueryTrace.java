package cache;

import sql.PrivacyQuery;

import java.util.*;

public class QueryTrace {
    // order of past queries is irrelevant, so using a map for cache lookup
    Map<String, List<QueryTraceEntry>> queries = new HashMap<>();
    QueryTraceEntry currentQuery = null;
    private int sz = 0;

    public void startQuery(PrivacyQuery query, List<Object> parameters) {
        if (currentQuery != null) {
            endQuery(Collections.emptyList());
        }
        currentQuery = new QueryTraceEntry(query, parameters);
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
