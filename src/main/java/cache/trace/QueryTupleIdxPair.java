package cache.trace;

import java.util.Objects;

public class QueryTupleIdxPair {
    private final int queryIdx;
    private final int tupleIdx;

    public QueryTupleIdxPair(int queryIdx, int tupleIdx) {
        this.queryIdx = queryIdx;
        this.tupleIdx = tupleIdx;
    }

    public int getQueryIdx() {
        return queryIdx;
    }

    public int getTupleIdx() {
        return tupleIdx;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        QueryTupleIdxPair that = (QueryTupleIdxPair) o;
        return queryIdx == that.queryIdx && tupleIdx == that.tupleIdx;
    }

    @Override
    public int hashCode() {
        return Objects.hash(queryIdx, tupleIdx);
    }
}
