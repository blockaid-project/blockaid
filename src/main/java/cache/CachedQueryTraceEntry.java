package cache;

import com.google.common.collect.Lists;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static com.google.common.base.Preconditions.checkState;

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

        @Override
        public String toString() {
            if (index != null) {
                return index.toString();
            } else {
                return variable;
            }
        }
    }

    private final String queryText;
    private final boolean isCurrentQuery;
    // exact value comparisons, null if value is irrelevant
    private final List<Object> parameters;
    private final List<List<Object>> tuples;
    // equalities - using indices shared across entire CachedQueryTrace, null if no constraint
    private final List<Index> parameterEquality;
    private final List<List<Index>> tupleEquality;

    private int maxEqualityNumber;
    private boolean isEmpty;

    public CachedQueryTraceEntry(QueryTraceEntry traceEntry, boolean isCurrentQuery, List<Index> parameterEquality, List<List<Index>> tupleEquality) {
        this(traceEntry.getParsedSql(), traceEntry.getParameters(), traceEntry.getTuples(), isCurrentQuery, parameterEquality, tupleEquality);
    }

    private CachedQueryTraceEntry(String queryText, List<Object> parameters, Iterable<List<Object>> tuples, boolean isCurrentQuery, List<Index> parameterEquality, List<List<Index>> tupleEquality) {
        this.queryText = queryText;
        this.isCurrentQuery = isCurrentQuery;
        this.parameters = parameters;
        this.tuples = Lists.newArrayList(tuples);
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
        removeDuplicateRows();
        checkEmpty();
    }

    private void removeDuplicateRows() {
        Set<List<Object>> seen = new HashSet<>();
        for (int i = tuples.size(); i-- > 0; ) {
            List<Object> key = new ArrayList<>(tuples.get(i));
            key.addAll(tupleEquality.get(i));
            if (seen.contains(key)) {
                tuples.remove(i);
                tupleEquality.remove(i);
            }
            seen.add(key);
        }
    }

    private void checkEmpty() {
        this.isEmpty = false;
        for (Object value : parameters) {
            if (value != null) {
                return;
            }
        }
        for (Index index : parameterEquality) {
            if (index != null) {
                return;
            }
        }
        this.isEmpty = tuples.isEmpty();
    }

    public boolean isEmpty() {
        return isEmpty;
    }

    public String getQueryText() {
        return queryText;
    }

    public int getMaxEqualityNumber() {
        return maxEqualityNumber;
    }

    public boolean isCurrentQuery() {
        return isCurrentQuery;
    }

    public boolean checkQueryText(QueryTraceEntry query) {
        return queryText.equals(query.getParsedSql());
    }

    public boolean checkParameters(QueryTraceEntry query, Map<Index, Object> mappedIndices) {
        Iterator<Object> cacheParamIter = parameters.iterator();
        Iterator<Object> queryParamIter = query.getParameters().iterator();
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
        checkState(!cacheParamIter.hasNext() && !queryParamIter.hasNext() && !paramEqualityIter.hasNext(),
                "cacheParam, queryParam, paramEquality should have the same size");
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
            checkState(!tupleIter.hasNext() && !equalityIter.hasNext());

            tupleChecks.add(completeTuple);
        }
        checkState(!cacheTupleIter.hasNext() && !tupleEqualityIter.hasNext(),
                "cacheTuple, tupleEquality must have the same size");

        return checkTuplesContained(tupleChecks.listIterator(), query.getTuples());
    }

    // TODO: is it okay to allow multiple tuples from cache to map to the same tuple in query
    private boolean checkTuplesContained(ListIterator<List<Object>> cacheTuples, Iterable<List<Object>> queryTuples) {
        if (!cacheTuples.hasNext()) {
            return true;
        }

        List<Object> cacheTuple = cacheTuples.next();

        // FIXME(zhangwen): this code can be simplified?
        Iterator<List<Object>> queryTupleIter = queryTuples.iterator();
        int i = 0;
        while (queryTupleIter.hasNext()) {
            List<Object> queryTuple = queryTupleIter.next();
            if (checkTupleEquality(cacheTuple, queryTuple)) {
                if (checkTuplesContained(cacheTuples, queryTuples)) {
                    return true;
                }
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
        checkState(!cacheTupleIter.hasNext() && !queryTupleIter.hasNext());

        return true;
    }

    @Override
    public String toString() {
        StringBuilder out = new StringBuilder();
        Pattern pattern = Pattern.compile("\\?");
        Matcher matcher = pattern.matcher(queryText);
        int i = 0;
        while (matcher.find()) {
            matcher.appendReplacement(out, "");
            if (parameters.get(i) != null) {
                out.append(parameters.get(i));
            } else if (parameterEquality.get(i) != null) {
                out.append("?").append(parameterEquality.get(i));
            } else {
                out.append("*");
            }
            ++i;
        }
        matcher.appendTail(out);
        out.append("\n");

        for (i = 0; i < tuples.size(); ++i) {
            out.append("\t(");
            boolean first = true;
            for (int j = 0; j < tuples.get(i).size(); ++j) {
                if (first) {
                    first = false;
                } else {
                    out.append(", ");
                }
                if (tuples.get(i).get(j) != null) {
                    out.append(tuples.get(i).get(j));
                } else if (tupleEquality.get(i).get(j) != null) {
                    out.append("?").append(tupleEquality.get(i).get(j));
                } else {
                    out.append("*");
                }
            }
            out.append(")\n");
        }
        return out.toString();
    }
}
