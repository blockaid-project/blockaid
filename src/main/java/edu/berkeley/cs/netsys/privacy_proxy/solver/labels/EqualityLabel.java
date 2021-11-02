package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import java.util.Collection;
import java.util.List;

public record EqualityLabel(Operand lhs, Operand rhs) implements Label {
    @Override
    public String toString() {
        return "EqualityLabel!" + lhs + "!" + rhs;
    }

    @Override
    public Kind getKind() {
        return Kind.EQUALITY;
    }

    @Override
    public Collection<Operand> getOperands() {
        return List.of(lhs, rhs);
    }
}
