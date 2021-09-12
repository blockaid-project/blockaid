package solver.labels;

import java.util.Objects;

public class ValueOperand implements Operand {
    private final Object value;

    public ValueOperand(Object value) {
        this.value = value;
    }

    public Object getValue() {
        return value;
    }

    @Override
    public Kind getKind() {
        return Kind.VALUE;
    }

    @Override
    public String toString() {
        return "ValueOperand_" + value;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ValueOperand that = (ValueOperand) o;
        return Objects.equals(value, that.value);
    }

    @Override
    public int hashCode() {
        return Objects.hash(value);
    }
}

