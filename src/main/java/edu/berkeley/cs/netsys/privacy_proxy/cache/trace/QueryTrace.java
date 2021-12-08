package edu.berkeley.cs.netsys.privacy_proxy.cache.trace;

import com.google.common.collect.*;
import edu.berkeley.cs.netsys.privacy_proxy.sql.ParserResult;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;

import java.sql.Timestamp;
import java.time.Duration;
import java.time.Instant;
import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class QueryTrace extends UnmodifiableLinearQueryTrace {
    private final ArrayListMultimap<ParserResult, QueryTraceEntry> queries;
    private final ArrayList<QueryTraceEntry> queryList; // Used to maintain order between queries.
    private QueryTraceEntry currentQuery;
    private Instant lastNow = null;

    // For de-duplication.
    private final HashSet<QueryTraceEntry> entrySet;

    // Maps constants to their values (e.g., _MY_UID -> 2).
    private final HashMap<String, Object> constMap;

    public QueryTrace() {
        queries = ArrayListMultimap.create();
        queryList = new ArrayList<>();
        currentQuery = null;
        entrySet = new HashSet<>();
        constMap = new HashMap<>();
    }

    private QueryTrace(ArrayListMultimap<ParserResult, QueryTraceEntry> queries, ArrayList<QueryTraceEntry> queryList,
                       QueryTraceEntry currentQuery, Instant lastNow, HashSet<QueryTraceEntry> entrySet,
                       HashMap<String, Object> constMap) {
        this.queries = ArrayListMultimap.create(queries);
        this.queryList = new ArrayList<>(queryList);
        this.currentQuery = currentQuery;
        this.lastNow = lastNow;
        this.entrySet = new HashSet<>(entrySet);
        this.constMap = new HashMap<>(constMap);
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

    public void startQuery(PrivacyQuery query) {
        if (currentQuery != null) {
            endQuery(Collections.emptyList());
        }
        for (int i = 0; i < query.paramNames.size(); ++i) {
            String name = query.paramNames.get(i);
            if (!name.equals("?")) {
                // Query can specify either parameter name or value, not both.
                checkArgument(query.parameters.get(i) == null);
            }
        }
        currentQuery = new QueryTraceEntry(query);
        queries.put(currentQuery.getParserResult(), currentQuery);
        queryList.add(currentQuery);
    }

    private void removeCurrentQuery() {
        List<QueryTraceEntry> bucket = queries.get(currentQuery.getParserResult());
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

    public Iterable<QueryTraceEntry> getEntriesByQuery(ParserResult pr) {
        return queries.get(pr);
    }

    public QueryTraceEntry getCurrentQuery() {
        return currentQuery;
    }

    public QueryTrace replaceCurrQuery(PrivacyQuery newQuery) {
        if (newQuery == currentQuery.getQuery()) {
            return this;
        }
        QueryTrace newTrace = new QueryTrace(queries, queryList, currentQuery, lastNow, entrySet, constMap);
        newTrace.endQueryDiscard();
        newTrace.startQuery(newQuery);
        return newTrace;
    }
}
