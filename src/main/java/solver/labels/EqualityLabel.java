package solver.labels;

import java.util.Collection;
import java.util.List;
import java.util.Objects;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

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
