package cache;

import cache.trace.QueryTrace;
import cache.trace.QueryTraceEntry;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableList;

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

    private final ArrayListMultimap<CacheKey, DecisionTemplate> compliantCache = ArrayListMultimap.create();
    private final ReadWriteLock lock = new ReentrantReadWriteLock();

    public Boolean checkCache(QueryTrace queryTrace) {
        Lock readLock = lock.readLock();
        readLock.lock();
        try {
            QueryTraceEntry currQuery = queryTrace.getCurrentQuery();
            CacheKey cacheKey = new CacheKey(currQuery.getParsedSql(), currQuery.getQuery().paramNames);
            List<DecisionTemplate> templates = compliantCache.get(cacheKey);
            ListIterator<DecisionTemplate> iterator = templates.listIterator(templates.size());
            while (iterator.hasPrevious()) {
                DecisionTemplate template = iterator.previous();
                if (template.doesMatch(queryTrace)) {
                    return true;
                }
            }
            return null;
        } finally {
            readLock.unlock();
        }
    }

    public void addCompliantToCache(String currentQuery, List<String> paramNames, DecisionTemplate template) {
        Lock writeLock = lock.writeLock();
        writeLock.lock();
        try {
            CacheKey cacheKey = new CacheKey(currentQuery, paramNames);
            compliantCache.put(cacheKey, template);
        } finally {
            writeLock.unlock();
        }
    }
}
