package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import java.util.Collection;
import java.util.List;

public record LessThanLabel(Operand lhs, Operand rhs) implements Label {
    @Override
    public String toString() {
        return "LessThanLabel!" + lhs + "!" + rhs;
    }

    @Override
    public Label.Kind getKind() {
        return Kind.LESS_THAN;
    }

    @Override
    public Collection<Operand> getOperands() {
        return List.of(lhs, rhs);
    }
}
