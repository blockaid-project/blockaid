package sql;

import java.util.*;

public class QuerySequence {
    private final ArrayList<QueryWithResult> trace;

    // Maps constants to their values (e.g., _MY_UID -> 2).
    // TODO(zhangwen): I hope this doesn't mess up caching.
    // TODO(zhangwen): The existing code seems to assume constants are integers (in ParsedPSJ.getPredicate),
    //  so I do the same here.
    private final HashMap<String, Integer> constMap;

    public QuerySequence() {
        this(new ArrayList<>(), new HashMap<>());
    }

    private QuerySequence(ArrayList<QueryWithResult> trace, HashMap<String, Integer> constMap) {
        this.trace = trace;
        this.constMap = constMap;
    }

    public QuerySequence copy() {
        ArrayList<QueryWithResult> newTrace = new ArrayList<>();
        for (QueryWithResult q : trace) {
            newTrace.add(q.copy());
        }

        HashMap<String, Integer> newConstMap = new HashMap<>(constMap);
        return new QuerySequence(newTrace, newConstMap);
    }

    public void setConstValue(String name, Integer value) {
        constMap.put(name, value);
    }

    /**
     * Gets a trace of all previous queries and their results.
     * @return a read-only view into the trace.
     */
    public List<QueryWithResult> getTrace() {
        return Collections.unmodifiableList(trace);
    }

    /**
     * Gets the constant map (constant name -> value).
     * @return a read-only view into the const map.
     */
    public Map<String, Integer> getConstMap() {
        return Collections.unmodifiableMap(constMap);
    }

    public void addToTrace(QueryWithResult q) {
        trace.add(q);
    }

    public QueryWithResult lastInTrace() {
        return trace.get(trace.size() - 1);
    }

    public void clear() {
        trace.clear();
        constMap.clear();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        QuerySequence that = (QuerySequence) o;
        return trace.equals(that.trace) && constMap.equals(that.constMap);
    }

    @Override
    public int hashCode() {
        return Objects.hash(trace, constMap);
    }
}
