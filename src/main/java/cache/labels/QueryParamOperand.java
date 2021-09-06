package cache.labels;

import java.util.Objects;

import static com.google.common.base.Preconditions.checkState;

public class QueryParamOperand implements Operand {
    private final int queryIdx;
    private final boolean isCurrentQuery;
    private final int paramIdx;

    public QueryParamOperand(int queryIdx, boolean isCurrentQuery, int paramIdx) {
        this.queryIdx = queryIdx;
        this.isCurrentQuery = isCurrentQuery;
        this.paramIdx = paramIdx;
    }

    // Should not be called if this is the current query.
    // TODO(zhangwen): this is ugly; maybe return a tagged enum.
    public int getQueryIdx() {
        checkState(!isCurrentQuery);
        return queryIdx;
    }

    public int getParamIdx() {
        return paramIdx;
    }

    public boolean isCurrentQuery() {
        return isCurrentQuery;
    }

    @Override
    public Kind getKind() {
        return Kind.QUERY_PARAM;
    }

    @Override
    public String toString() {
        return "QueryParamOperand_" + (isCurrentQuery ? "curr" : queryIdx) + "_" + paramIdx;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        QueryParamOperand that = (QueryParamOperand) o;
        return queryIdx == that.queryIdx && isCurrentQuery == that.isCurrentQuery && paramIdx == that.paramIdx;
    }

    @Override
    public int hashCode() {
        return Objects.hash(queryIdx, isCurrentQuery, paramIdx);
    }
}

