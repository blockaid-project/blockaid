package cache;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Multimap;

import java.util.*;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

public class TraceCache {
    private static class CacheKey {
        private final String sql;
        private final ImmutableList<String> paramNames;

        public CacheKey(String sql, Iterable<String> paramNames) {
            this.sql = sql;
            this.paramNames = ImmutableList.copyOf(paramNames);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            CacheKey cacheKey = (CacheKey) o;
            return Objects.equals(sql, cacheKey.sql) &&
                    Objects.equals(paramNames, cacheKey.paramNames);
        }

        @Override
        public int hashCode() {
            return Objects.hash(sql, paramNames);
        }
    }
    private static class Entry {
        private final CachedQueryTrace trace;
        private final boolean compliance;

        public Entry(CachedQueryTrace trace, boolean compliance) {
            this.trace = trace;
            this.compliance = compliance;
        }
    }
    private final ArrayListMultimap<CacheKey, Entry> cache = ArrayListMultimap.create();
    private final ReadWriteLock lock = new ReentrantReadWriteLock();

    public Boolean checkCache(QueryTrace queryTrace) {
        Lock readLock = lock.readLock();
        readLock.lock();
        try {
            QueryTraceEntry currQuery = queryTrace.getCurrentQuery();
            CacheKey cacheKey = new CacheKey(currQuery.getParsedSql(), currQuery.getQuery().paramNames);
            List<Entry> entryList = cache.get(cacheKey);
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

    public void addToCache(String currentQuery, List<String> paramNames, CachedQueryTrace cachedQueryTrace, boolean compliance) {
        Lock writeLock = lock.writeLock();
        writeLock.lock();
        try {
            CacheKey cacheKey = new CacheKey(currentQuery, paramNames);
            cache.put(cacheKey, new Entry(cachedQueryTrace, compliance));
        } finally {
            writeLock.unlock();
        }
    }
}
