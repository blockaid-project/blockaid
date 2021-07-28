package cache;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Multimap;
import sql.PrivacyQuery;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;

public class QueryTrace {
    // order of past queries is irrelevant, so using a map for cache lookup
    private final Multimap<String, QueryTraceEntry> queries = ArrayListMultimap.create();
    private QueryTraceEntry currentQuery = null;

    // Maps constants to their values (e.g., _MY_UID -> 2).
    // TODO(zhangwen): The existing code seems to assume constants are integers (in ParsedPSJ.getPredicate),
    //  so I do the same here.
    private final HashMap<String, Integer> constMap = new HashMap<>();

    public void setConstValue(String name, Integer value) {
        constMap.put(name, value);
    }

    /**
     * Gets the constant map (constant name -> value).
     * @return a read-only view into the const map.
     */
    public Map<String, Integer> getConstMap() {
        return Collections.unmodifiableMap(constMap);
    }

    public void startQuery(PrivacyQuery query, List<Object> parameters) {
        if (currentQuery != null) {
            endQuery(Collections.emptyList());
        }
        currentQuery = new QueryTraceEntry(query, parameters);
        queries.put(query.parsedSql.getParsedSql(), currentQuery);
    }

    public void endQuery(List<List<Object>> tuples) {
        checkState(currentQuery != null);
        currentQuery.setTuples(tuples);
        currentQuery = null;
    }

    public Iterable<QueryTraceEntry> getAllEntries() {
        return queries.values();
    }

    public Iterable<QueryTraceEntry> getEntriesByText(String queryText) {
        return queries.get(queryText);
    }

    public QueryTraceEntry getCurrentQuery() {
        return currentQuery;
    }

    public int size() {
        return queries.size();
    }
}
