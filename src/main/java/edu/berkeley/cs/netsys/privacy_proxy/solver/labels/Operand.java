package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

public interface Operand {
    enum Kind {
        CONTEXT_CONSTANT,
        QUERY_PARAM,
        RETURNED_ROW_ATTR,
        VALUE,
    }

    Kind getKind();
}
