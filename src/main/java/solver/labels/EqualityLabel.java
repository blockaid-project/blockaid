package solver.labels;

import java.util.Collection;
import java.util.List;
import java.util.Objects;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public class EqualityLabel implements Label {
    private final Operand lhs;
    private final Operand rhs;

    public EqualityLabel(Operand lhs, Operand rhs) {
        this.lhs = checkNotNull(lhs);
        this.rhs = checkNotNull(rhs);
    }

    @Override
    public String toString() {
        return "EqualityLabel!" + lhs + "!" + rhs;
    }

    public Operand getLhs() {
        return lhs;
    }

    public Operand getRhs() {
        return rhs;
    }

    @Override
    public Kind getKind() {
        return Kind.EQUALITY;
    }

    @Override
    public Collection<Operand> getOperands() {
        return List.of(lhs, rhs);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        EqualityLabel that = (EqualityLabel) o;
        return lhs.equals(that.lhs) && rhs.equals(that.rhs);
    }

    @Override
    public int hashCode() {
        return Objects.hash(lhs, rhs);
    }
}
