package cache;

import java.util.*;

public class CachedQueryTraceEntry {
    public static class Index {
        public Integer index = null;
        public String variable = null;

        public Index(Integer index) {
            this.index = index;
        }

        public Index(String variable) {
            this.variable = variable;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Index index1 = (Index) o;
            return Objects.equals(index, index1.index) &&
                    Objects.equals(variable, index1.variable);
        }

        @Override
        public int hashCode() {
            return Objects.hash(index, variable);
        }
    }

    private String queryText;
    // exact value comparisons, null if value is irrelevant
    private List<Object> parameters;
    private List<List<Object>> tuples;
    // equalities - using indices shared across entire CachedQueryTrace, null if no constraint
    private List<Index> parameterEquality;
    private List<List<Index>> tupleEquality;

    private int maxEqualityNumber;

    public CachedQueryTraceEntry(QueryTraceEntry trace, List<Index> parameterEquality, List<List<Index>> tupleEquality) {
        this(trace.query.parsedSql.getParsedSql(), trace.parameters, trace.tuples, parameterEquality, tupleEquality);
    }

    private CachedQueryTraceEntry(String queryText, List<Object> parameters, List<List<Object>> tuples, List<Index> parameterEquality, List<List<Index>> tupleEquality) {
        this.queryText = queryText;
        this.parameters = parameters;
        this.tuples = tuples;
        this.parameterEquality = parameterEquality;
        this.tupleEquality = tupleEquality;

        this.maxEqualityNumber = 0;
        for (Index index : parameterEquality) {
            if (index != null && index.index != null) {
                this.maxEqualityNumber = Math.max(this.maxEqualityNumber, index.index);
            }
        }
        for (List<Index> tuple : tupleEquality) {
            for (Index index : tuple) {
                if (index != null && index.index != null) {
                    this.maxEqualityNumber = Math.max(this.maxEqualityNumber, index.index);
                }
            }
        }
    }

    public String getQueryText() {
        return queryText;
    }

    public int getMaxEqualityNumber() {
        return maxEqualityNumber;
    }

    public boolean checkQueryText(QueryTraceEntry query) {
        return queryText.equals(query.query.parsedSql.getParsedSql());
    }

    public boolean checkParameters(QueryTraceEntry query, Map<Index, Object> mappedIndices) {
        Iterator<Object> cacheParamIter = parameters.iterator();
        Iterator<Object> queryParamIter = query.parameters.iterator();
        Iterator<Index> paramEqualityIter = parameterEquality.iterator();

        while (cacheParamIter.hasNext() && queryParamIter.hasNext() && paramEqualityIter.hasNext()) {
            Index equalityIndex = paramEqualityIter.next();
            Object cacheValue = cacheParamIter.next();
            Object queryValue = queryParamIter.next();
            if (cacheValue != null && !cacheValue.equals(queryValue)) {
                return false;
            }
            if (equalityIndex != null) {
                if (mappedIndices.containsKey(equalityIndex) && !mappedIndices.get(equalityIndex).equals(queryValue)) {
                    return false;
                }
                mappedIndices.put(equalityIndex, queryValue);
            }
        }
        assert !cacheParamIter.hasNext() && !queryParamIter.hasNext() && !paramEqualityIter.hasNext();
        return true;
    }

    public boolean checkValues(QueryTraceEntry query, Map<Index, Object> mappedIndices) {
        // assuming that there are no new parameters in tuples; copy of tuples with equalities filled in
        List<List<Object>> tupleChecks = new ArrayList<>();

        Iterator<List<Object>> cacheTupleIter = tuples.iterator();
        Iterator<List<Index>> tupleEqualityIter = tupleEquality.iterator();
        while (cacheTupleIter.hasNext() && tupleEqualityIter.hasNext()) {
            List<Object> completeTuple = new ArrayList<>(cacheTupleIter.next());
            List<Index> equality = tupleEqualityIter.next();

            ListIterator<Object> tupleIter = completeTuple.listIterator();
            Iterator<Index> equalityIter = equality.iterator();
            while (tupleIter.hasNext() && equalityIter.hasNext()) {
                Index index = equalityIter.next();
                tupleIter.next();
                if (index != null) {
                    tupleIter.set(mappedIndices.get(index));
                }
            }
            assert !tupleIter.hasNext() && !equalityIter.hasNext();

            tupleChecks.add(completeTuple);
        }
        assert !cacheTupleIter.hasNext() && !tupleEqualityIter.hasNext();

        return checkTuplesContained(tupleChecks.listIterator(), query.tuples, new boolean[query.tuples.size()]);
    }

    // TODO: is it okay to allow multiple tuples from cache to map to the same tuple in query
    private boolean checkTuplesContained(ListIterator<List<Object>> cacheTuples, List<List<Object>> queryTuples, boolean[] used) {
        if (!cacheTuples.hasNext()) {
            return true;
        }

        List<Object> cacheTuple = cacheTuples.next();

        Iterator<List<Object>> queryTupleIter = queryTuples.iterator();
        int i = 0;
        while (queryTupleIter.hasNext()) {
            List<Object> queryTuple = queryTupleIter.next();
            if (!used[i] && checkTupleEquality(cacheTuple, queryTuple)) {
                used[i] = true;
                if (checkTuplesContained(cacheTuples, queryTuples, used)) {
                    return true;
                }
                used[i] = false;
            }
            ++i;
        }

        cacheTuples.previous();

        return false;
    }

    private boolean checkTupleEquality(List<Object> cacheTuple, List<Object> queryTuple) {
        Iterator<Object> cacheTupleIter = cacheTuple.iterator();
        Iterator<Object> queryTupleIter = queryTuple.iterator();

        while (cacheTupleIter.hasNext() && queryTupleIter.hasNext()) {
            Object cacheValue = cacheTupleIter.next();
            Object queryValue = queryTupleIter.next();

            if (cacheValue != null && !cacheValue.equals(queryValue)) {
                return false;
            }
        }
        assert !cacheTupleIter.hasNext() && !queryTupleIter.hasNext();

        return true;
    }
}
