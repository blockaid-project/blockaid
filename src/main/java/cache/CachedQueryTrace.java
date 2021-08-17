package cache;

import java.util.*;

public class CachedQueryTrace {
    private List<CachedQueryTraceEntry> entries = new ArrayList<>();
    private Map<String, Integer> constEqualities = new HashMap<>();

    public CachedQueryTrace() {}

    public CachedQueryTrace(CachedQueryTrace other) {
        entries = new ArrayList<>(other.entries);
        constEqualities = new HashMap<>(constEqualities);
    }

    public void addEntry(CachedQueryTraceEntry entry) {
        entries.add(entry);
    }

    public void addVariable(String name, Integer index) {
        constEqualities.put(name, index);
    }

    public boolean checkQueryTrace(QueryTrace trace) {
        return checkQueryTrace(entries.listIterator(), trace, new ArrayList<>());
    }

    // TODO assuming that multiple queries in cache entry may be mapped to same query trace query - is this ok?
    private boolean checkQueryTrace(ListIterator<CachedQueryTraceEntry> entries, QueryTrace trace, List<QueryTraceEntry> usedEntries) {
        if (!entries.hasNext()) {
            Map<Integer, Object> mappedIndices = new HashMap<>();
            // mappedIndices is populated through query parameters, including those of later queries, so
            // all queries' parameters/variables must be processed before any query's values
            Iterator<CachedQueryTraceEntry> cacheEntries = this.entries.iterator();
            for (QueryTraceEntry traceEntry : usedEntries) {
                CachedQueryTraceEntry cacheEntry = cacheEntries.next();
                if (!cacheEntry.checkParameters(traceEntry, mappedIndices)) {
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
            for (Map.Entry<String, Integer> c : trace.getConstMap().entrySet()) {
                String name = c.getKey();
                Integer value = c.getValue();
                if (constEqualities.containsKey(name)) {
                    Integer index = constEqualities.get(name);
                    if (index != null && !mappedIndices.get(index).equals(value)) {
                        return false;
                    }
                }
            }
            return true;
        }

        CachedQueryTraceEntry cacheEntry = entries.next();

        if (cacheEntry.isCurrentQuery()) {
            QueryTraceEntry traceEntry = trace.getCurrentQuery();
            if (cacheEntry.checkQueryText(traceEntry)) {
                usedEntries.add(traceEntry);
                if (checkQueryTrace(entries, trace, usedEntries)) {
                    return true;
                }
                usedEntries.remove(usedEntries.size() - 1);
            }
        } else {
            for (QueryTraceEntry traceEntry : trace.getEntriesByText(cacheEntry.getQueryText())) {
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

    @Override
    public String toString() {
        StringBuilder s = new StringBuilder("---------------\n");
        for (CachedQueryTraceEntry trace : entries) {
            if (!trace.isCurrentQuery()) {
                s.append(trace);
            }
        }
        for (CachedQueryTraceEntry trace : entries) {
            if (trace.isCurrentQuery()) {
                s.append(trace);
            }
        }
        s.append("Constants:\n");
        for (Map.Entry<String, Integer> variable : constEqualities.entrySet()) {
            s.append("\t").append(variable.getKey()).append(" = ");
            if (variable.getValue() == null) {
                s.append("*");
            } else {
                s.append("?").append(variable.getValue());
            }
            s.append("\n");
        }
        s.append("---------------\n");
        return s.toString();
    }
}
