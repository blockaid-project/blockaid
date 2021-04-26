package cache;

import java.util.*;

public class CachedQueryTrace {
    private List<CachedQueryTraceEntry> entries = new ArrayList<>();
    private int numEqualities = 0;

    public CachedQueryTrace() {}

    public CachedQueryTrace(CachedQueryTrace other) {
        entries = new ArrayList<>(other.entries);
        numEqualities = other.numEqualities;
    }

    public void addEntry(CachedQueryTraceEntry entry) {
        numEqualities = Math.max(numEqualities, entry.getMaxEqualityNumber());
        entries.add(entry);
    }

    public int getNumEqualities() {
        return numEqualities;
    }

    public boolean checkQueryTrace(QueryTrace trace) {
        return checkQueryTrace(entries.listIterator(), trace, new ArrayList<>());
    }

    // TODO assuming that multiple queries in cache entry may be mapped to same query trace query - is this ok?
    private boolean checkQueryTrace(ListIterator<CachedQueryTraceEntry> entries, QueryTrace trace, List<QueryTraceEntry> usedEntries) {
        if (!entries.hasNext()) {
            Map<CachedQueryTraceEntry.Index, Object> mappedIndices = new HashMap<>();
            // variables
            for (List<QueryTraceEntry> e : trace.queries.values()) {
                for (QueryTraceEntry entry : e) {
                    for (Map.Entry<String, Object> variable : entry.variables.entrySet()) {
                        CachedQueryTraceEntry.Index index = new CachedQueryTraceEntry.Index(variable.getKey());
                        if (mappedIndices.containsKey(index) && !mappedIndices.get(index).equals(variable.getValue())) {
                            return false;
                        }
                        mappedIndices.put(index, variable.getValue());
                    }
                }
            }
            // mappedIndices is populated through query parameters, including those of later queries, so
            // all queries' parameters/variables must be processed before any query's values
            Iterator<CachedQueryTraceEntry> cacheEntries = this.entries.iterator();
            for (QueryTraceEntry entry : usedEntries) {
                CachedQueryTraceEntry cacheEntry = cacheEntries.next();
                if (!cacheEntry.checkParameters(entry, mappedIndices)) {
                    return false;
                }
            }
            cacheEntries = this.entries.iterator();
            for (QueryTraceEntry entry : usedEntries) {
                CachedQueryTraceEntry cacheEntry = cacheEntries.next();
                if (!cacheEntry.checkValues(entry, mappedIndices)) {
                    return false;
                }
            }
            return true;
        }

        CachedQueryTraceEntry cacheEntry = entries.next();

        if (trace.queries.containsKey(cacheEntry.getQueryText())) {
            for (QueryTraceEntry traceEntry : trace.queries.get(cacheEntry.getQueryText())) {
                if (cacheEntry.checkQueryText(traceEntry)) {
                    usedEntries.add(traceEntry);
                    if (checkQueryTrace(entries, trace, usedEntries)) {
                        return true;
                    }
                    usedEntries.remove(usedEntries.size() - 1);
                }
            }
        }

        entries.previous();
        return false;
    }
}
