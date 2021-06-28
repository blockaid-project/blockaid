package cache;

import java.util.*;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

public class TraceCache {
    private static class Entry {
        private final CachedQueryTrace trace;
        private final boolean compliance;

        public Entry(CachedQueryTrace trace, boolean compliance) {
            this.trace = trace;
            this.compliance = compliance;
        }
    }
    private final Map<String, List<Entry>> cache = new HashMap<>();
    private final ReadWriteLock lock = new ReentrantReadWriteLock();

    public Boolean checkCache(QueryTrace queryTrace) {
        Lock readLock = lock.readLock();
        readLock.lock();
        try {
            List<Entry> entryList = cache.getOrDefault(queryTrace.getCurrentQuery().getParsedSql(), Collections.emptyList());
            ListIterator<Entry> iterator = entryList.listIterator(entryList.size());
            while (iterator.hasPrevious()) {
                Entry entry = iterator.previous();
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
