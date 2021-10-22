package edu.berkeley.cs.netsys.privacy_proxy.cache;

import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTrace;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableList;
import edu.berkeley.cs.netsys.privacy_proxy.sql.ParserResult;

import java.util.*;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

public class TraceCache {
    private record CacheKey(ParserResult sql, ImmutableList<String> paramNames) {
        public CacheKey(ParserResult sql, Collection<String> paramNames) {
            this(sql, ImmutableList.copyOf(paramNames));
        }
    }

    private final ArrayListMultimap<CacheKey, DecisionTemplate> compliantCache = ArrayListMultimap.create();
    private final ReadWriteLock lock = new ReentrantReadWriteLock();

    public Boolean checkCache(QueryTrace queryTrace) {
        Lock readLock = lock.readLock();
        readLock.lock();
        try {
            QueryTraceEntry currQuery = queryTrace.getCurrentQuery();
            CacheKey cacheKey = new CacheKey(currQuery.getParserResult(), currQuery.getQuery().paramNames);
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

    public void addCompliantToCache(ParserResult currentQuery, List<String> paramNames, DecisionTemplate template) {
        Lock writeLock = lock.writeLock();
        writeLock.lock();
        try {
            CacheKey cacheKey = new CacheKey(currentQuery, paramNames);
            compliantCache.put(cacheKey, template);
        } finally {
            writeLock.unlock();
        }
    }

    public void clear() {
        Lock writeLock = lock.writeLock();
        writeLock.lock();
        try {
            compliantCache.clear();
        } finally {
            writeLock.unlock();
        }
    }
}
