package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import edu.berkeley.cs.netsys.privacy_proxy.solver.Constraint;

public record ConstraintLabel(Constraint constraint) implements PreambleLabel {
    @Override
    public Kind getKind() {
        return Kind.CONSTRAINT;
    }
}
