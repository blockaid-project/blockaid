package cache.trace;

import com.google.common.collect.ImmutableMap;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class SubQueryTrace extends UnmodifiableLinearQueryTrace {
    private final List<QueryTraceEntry> queryList;
    private final Map<String, Object> constMap;
    private final QueryTraceEntry currentQuery;
    private final ImmutableMap<QueryTupleIdxPair, QueryTupleIdxPair> backMap;
    private final ImmutableMap<Integer, Integer> queryIdxBackMap;

    SubQueryTrace(List<QueryTraceEntry> queryList, Map<String, Object> constMap,
                  QueryTraceEntry currentQuery,
                  Map<QueryTupleIdxPair, QueryTupleIdxPair> backMap) {
        this.queryList = checkNotNull(queryList);
        this.constMap = checkNotNull(constMap);
        this.currentQuery = checkNotNull(currentQuery);
        this.backMap = ImmutableMap.copyOf(backMap);

        HashMap<Integer, Integer> queryIdxBackMap = new HashMap<>();
        for (Map.Entry<QueryTupleIdxPair, QueryTupleIdxPair> e : backMap.entrySet()) {
            int oldQueryIdx = e.getValue().queryIdx();
            Integer original = queryIdxBackMap.putIfAbsent(e.getKey().queryIdx(), oldQueryIdx);
            if (original != null) {
                checkArgument(original == oldQueryIdx);
            }
        }
        this.queryIdxBackMap = ImmutableMap.copyOf(queryIdxBackMap);
    }

    @Override
    public Map<String, Object> getConstMap() {
        return Collections.unmodifiableMap(constMap);
    }

    @Override
    public List<QueryTraceEntry> getAllEntries() {
        return Collections.unmodifiableList(queryList);
    }

    @Override
    public QueryTraceEntry getCurrentQuery() {
        return currentQuery;
    }

    public ImmutableMap<QueryTupleIdxPair, QueryTupleIdxPair> getBackMap() {
        return backMap;
    }

    public ImmutableMap<Integer, Integer> getQueryIdxBackMap() {
        return queryIdxBackMap;
    }
}
