package edu.berkeley.cs.netsys.privacy_proxy.util;

import org.apache.calcite.sql.SqlCall;

public class SqlNodes {
    // This is the same as `SqlCall.clone`, but the overridden version from `SqlBasicCall.clone` doesn't perform a deep
    // copy, so use this method to deep copy a `SqlBasicCall` (or any `SqlCall`, really).
    public static <T extends SqlCall> T shallowCopy(T c) {
        //noinspection unchecked
        return (T) c.getOperator().createCall(c.getFunctionQuantifier(), c.getParserPosition(), c.getOperandList());
    }
}
