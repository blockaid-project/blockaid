package cache;

import java.util.*;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

public class TraceCache {
    private class Entry {
        private CachedQueryTrace trace;
        private boolean compliance;

        public Entry(CachedQueryTrace trace, boolean compliance) {
            this.trace = trace;
            this.compliance = compliance;
        }
    }
    private Map<String, List<Entry>> cache = new HashMap<>();
    private ReadWriteLock lock = new ReentrantReadWriteLock();

    public Boolean checkCache(QueryTrace queryTrace) {
        Lock readLock = lock.readLock();
        readLock.lock();
        try {
            for (Entry entry : cache.getOrDefault(queryTrace.currentQuery.getQuery().parsedSql.getParsedSql(), Collections.emptyList())) {
                if (entry.trace.checkQueryTrace(queryTrace)) {
                    return entry.compliance;
                }
            }
            return null;
        } finally {
            readLock.unlock();
        }
    }

    public void addToCache(String currentQuery, CachedQueryTrace cachedQueryTrace, boolean compliance) {
        Lock writeLock = lock.writeLock();
        writeLock.lock();
        try {
            cache.putIfAbsent(currentQuery, new ArrayList<>());
            cache.get(currentQuery).add(new Entry(cachedQueryTrace, compliance));
        } finally {
            writeLock.unlock();
        }
    }
}
