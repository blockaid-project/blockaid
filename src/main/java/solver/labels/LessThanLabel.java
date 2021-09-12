package solver.labels;

import java.util.Collection;
import java.util.List;
import java.util.Objects;

import static com.google.common.base.Preconditions.checkNotNull;

public class LessThanLabel implements Label {
    private final Operand lhs;
    private final Operand rhs;

    public LessThanLabel(Operand lhs, Operand rhs) {
        this.lhs = checkNotNull(lhs);
        this.rhs = checkNotNull(rhs);
    }

    @Override
    public String toString() {
        return "LessThanLabel!" + lhs + "!" + rhs;
    }

    public Operand getLhs() {
        return lhs;
    }

    public Operand getRhs() {
        return rhs;
    }

    @Override
    public Label.Kind getKind() {
        return Kind.LESS_THAN;
    }

    @Override
    public Collection<Operand> getOperands() {
        return List.of(lhs, rhs);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        LessThanLabel that = (LessThanLabel) o;
        return lhs.equals(that.lhs) && rhs.equals(that.rhs);
    }

    @Override
    public int hashCode() {
        return Objects.hash(lhs, rhs);
    }
}
