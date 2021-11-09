package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import java.util.Collection;
import java.util.Collections;

public record ReturnedRowLabel(int queryIdx, int rowIdx) implements Label {
    @Override
    public Kind getKind() {
        return Kind.RETURNED_ROW;
    }

    @Override
    public Collection<Operand> getOperands() {
        return Collections.emptyList();
    }

    @Override
    public String toString() {
        return "ReturnedRowLabel_" + queryIdx + "_" + rowIdx;
    }
}
