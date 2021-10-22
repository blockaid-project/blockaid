package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import static com.google.common.base.Preconditions.checkState;

public record QueryParamOperand(int queryIdx, boolean isCurrentQuery, int paramIdx) implements Operand {
    // Should not be called if this is the current query.
    // TODO(zhangwen): this is ugly; maybe return a tagged enum.
    @Override
    public int queryIdx() {
        checkState(!isCurrentQuery);
        return queryIdx;
    }

    @Override
    public Kind getKind() {
        return Kind.QUERY_PARAM;
    }

    @Override
    public String toString() {
        return "QueryParamOperand_" + (isCurrentQuery ? "curr" : queryIdx) + "_" + paramIdx;
    }
}
