package solver.labels;

import solver.Constraint;

public record ConstraintLabel(Constraint constraint) implements PreambleLabel {
    @Override
    public Kind getKind() {
        return Kind.CONSTRAINT;
    }
}
