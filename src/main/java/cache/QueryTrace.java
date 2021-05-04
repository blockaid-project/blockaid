package cache;

import sql.PrivacyQuery;

import java.util.*;

public class QueryTrace {
    // order of past queries is irrelevant, so using a map for cache lookup
    Map<String, List<QueryTraceEntry>> queries = new HashMap<>();
    QueryTraceEntry currentQuery = null;
    private int sz = 0;

    // Maps constants to their values (e.g., _MY_UID -> 2).
    // TODO(zhangwen): The existing code seems to assume constants are integers (in ParsedPSJ.getPredicate),
    //  so I do the same here.
//    private final HashMap<String, Integer> constMap = new HashMap<>();
    private final HashMap<Long, String> constMapReversed = new HashMap<>();

    public void setConstValue(String name, Long value) {
//        constMap.put(name, value);
        if (constMapReversed.containsKey(value)) {
            throw new RuntimeException("currently not supported: multiple consts with the same value");
        }
        constMapReversed.put(value, name);
    }

    /**
     * Gets the constant map (constant name -> value).
     * @return a read-only view into the const map.
     */
//    public Map<String, Integer> getConstMap() {
//        return Collections.unmodifiableMap(constMap);
//    }

    public Map<Long, String> getReverseConstMap() {
        return Collections.unmodifiableMap(constMapReversed);
    }

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
