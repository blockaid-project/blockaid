package cache;

import com.google.common.collect.ArrayListMultimap;
import sql.PrivacyQuery;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class QueryTrace {
    private final ArrayListMultimap<String, QueryTraceEntry> queries = ArrayListMultimap.create();
    private final ArrayList<QueryTraceEntry> queryList = new ArrayList<>(); // Used to maintain order between queries.
    private QueryTraceEntry currentQuery = null;

    // For de-duplication.
    private final HashSet<QueryTraceEntry> entrySet = new HashSet<>();

    // Maps constants to their values (e.g., _MY_UID -> 2).
    // TODO(zhangwen): The existing code seems to assume constants are integers (in ParsedPSJ.getPredicate),
    //  so I do the same here.
    private final HashMap<String, Integer> constMap = new HashMap<>();

    public void setConstValue(String name, Integer value) {
        checkArgument(constMap.getOrDefault(name, value).equals(value));
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
        for (int i = 0; i < query.paramNames.size(); ++i) {
            String name = query.paramNames.get(i);
            if (!name.equals("?")) {
                // Query can specify either parameter name or value, not both.
                checkArgument(parameters.get(i) == null);
            }
        }
        currentQuery = new QueryTraceEntry(query, parameters);
        queries.put(currentQuery.getParsedSql(), currentQuery);
        queryList.add(currentQuery);
    }

    public void endQuery(List<List<Object>> tuples) {
        checkState(currentQuery != null);
        currentQuery.setTuples(tuples);

        if (!entrySet.add(currentQuery)) {
            // The current query is a duplicate.  Remove!
            List<QueryTraceEntry> bucket = queries.get(currentQuery.getParsedSql());
            bucket.remove(bucket.size() - 1);
            queryList.remove(queryList.size() - 1);
        }

        currentQuery = null;
    }

    public List<QueryTraceEntry> getAllEntries() {
        return Collections.unmodifiableList(queryList);
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
