package cache.trace;

import com.google.common.collect.*;
import sql.PrivacyQuery;

import java.sql.Timestamp;
import java.time.Duration;
import java.time.Instant;
import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class QueryTrace extends UnmodifiableLinearQueryTrace {
    private final ArrayListMultimap<String, QueryTraceEntry> queries;
    private final ArrayList<QueryTraceEntry> queryList; // Used to maintain order between queries.
    private QueryTraceEntry currentQuery;
    private Instant lastNow = null;

    // For de-duplication.
    private final HashSet<QueryTraceEntry> entrySet;

    // Maps constants to their values (e.g., _MY_UID -> 2).
    // TODO(zhangwen): The existing code seems to assume constants are integers (in ParsedPSJ.getPredicate),
    //  so I do the same here.
    private final HashMap<String, Object> constMap;

    public QueryTrace() {
        queries = ArrayListMultimap.create();
        queryList = new ArrayList<>();
        currentQuery = null;
        entrySet = new HashSet<>();
        constMap = new HashMap<>();
    }

    public void setConstValue(String name, Object value) {
        checkArgument(constMap.getOrDefault(name, value).equals(value));
        constMap.put(name, value);
    }

    /**
     * Gets the constant map (constant name -> value).
     * @return a read-only view into the const map.
     */
    public Map<String, Object> getConstMap() {
        Instant now = Instant.now();
        // HACK: it's probably unnecessary to generate too many "now" timestamps that are close to each other.
        // A more proper way would be to remove "now" from tracked constants after each formula generation.
        if (lastNow == null || Duration.between(lastNow, now).getSeconds() >= 60) {
            lastNow = now;
        }
        HashMap<String, Object> cm = new HashMap<>(constMap);
        cm.put("_NOW", Timestamp.from(lastNow));
        return Collections.unmodifiableMap(cm);
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

    private void removeCurrentQuery() {
        List<QueryTraceEntry> bucket = queries.get(currentQuery.getParsedSql());
        bucket.remove(bucket.size() - 1);
        queryList.remove(queryList.size() - 1);
    }

    public void endQueryDiscard() {
        checkState(currentQuery != null);
        removeCurrentQuery();
        currentQuery = null;
    }

    public void endQuery(List<List<Object>> tuples) {
        checkState(currentQuery != null);
        currentQuery.setTuples(tuples);

        if (!entrySet.add(currentQuery)) {
            // The current query is a duplicate.  Remove!
            removeCurrentQuery();
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
}
