package edu.berkeley.cs.netsys.privacy_proxy.cache;

import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import com.google.common.collect.Lists;
import edu.berkeley.cs.netsys.privacy_proxy.sql.ParserResult;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static com.google.common.base.Preconditions.checkState;

public class CachedQueryTraceEntry {
    private final ParserResult qpr;
    private final boolean isCurrentQuery;
    private final List<Object> parameters; // exact value comparisons, null if value is irrelevant
    private final List<List<Object>> tuples;

    // equalities - using indices shared across entire CachedQueryTrace, null if no constraint
    private final List<Integer> parameterEquality;

    private final List<List<Integer>> tupleEquality;

    private boolean isEmpty;

    private CachedQueryTraceEntry(ParserResult qpr, List<Object> parameters, Iterable<List<Object>> tuples, boolean isCurrentQuery, List<Integer> parameterEquality, List<List<Integer>> tupleEquality) {
        this.qpr = qpr;
        this.isCurrentQuery = isCurrentQuery;
        this.parameters = parameters;
        this.tuples = Lists.newArrayList(tuples);
        this.parameterEquality = parameterEquality;
        this.tupleEquality = tupleEquality;

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
        for (Integer index : parameterEquality) {
            if (index != null) {
                return;
            }
        }
        this.isEmpty = tuples.isEmpty();
    }

    public boolean isEmpty() {
        return isEmpty;
    }

    public ParserResult getQuery() {
        return qpr;
    }

    public boolean isCurrentQuery() {
        return isCurrentQuery;
    }

    public boolean checkQuery(QueryTraceEntry qte) {
        return qpr.equals(qte.getParserResult());
    }

    // Updates mappedIndices with encountered indices.
    public boolean checkParameters(QueryTraceEntry query, Map<Integer, Object> mappedIndices) {
        Iterator<Object> cacheParamIter = parameters.iterator();
        Iterator<Object> queryParamIter = query.getParameters().iterator();
        Iterator<Integer> paramEqualityIter = parameterEquality.iterator();

        while (cacheParamIter.hasNext() && queryParamIter.hasNext() && paramEqualityIter.hasNext()) {
            Object cacheValue = cacheParamIter.next();
            Object queryValue = queryParamIter.next();
            Integer equalityIndex = paramEqualityIter.next();
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

    public boolean checkValues(QueryTraceEntry query, Map<Integer, Object> mappedIndices) {
        // assuming that there are no new parameters in tuples; copy of tuples with equalities filled in
        List<List<Object>> tupleChecks = new ArrayList<>();

        Iterator<List<Object>> cacheTupleIter = tuples.iterator();
        Iterator<List<Integer>> tupleEqualityIter = tupleEquality.iterator();
        while (cacheTupleIter.hasNext() && tupleEqualityIter.hasNext()) {
            List<Object> completeTuple = new ArrayList<>(cacheTupleIter.next());
            List<Integer> equality = tupleEqualityIter.next();

            ListIterator<Object> tupleIter = completeTuple.listIterator();
            Iterator<Integer> equalityIter = equality.iterator();
            while (tupleIter.hasNext() && equalityIter.hasNext()) {
                Integer index = equalityIter.next();
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
        // TODO(zhangwen): a question mark might not denote a parameter (e.g., if it's in a string).
        Pattern pattern = Pattern.compile("\\?");
        Matcher matcher = pattern.matcher(qpr.getParsedSql());
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
