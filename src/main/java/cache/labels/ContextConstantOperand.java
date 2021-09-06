package cache.labels;

import java.util.Objects;

import static com.google.common.base.Preconditions.checkNotNull;

public class ContextConstantOperand implements Operand {
    private final String name;

    public ContextConstantOperand(String name) {
        this.name = checkNotNull(name);
    }

    public String getName() {
        return name;
    }

    @Override
    public String toString() {
        return "ContextConstantOperand_" + name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ContextConstantOperand that = (ContextConstantOperand) o;
        return name.equals(that.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }

    @Override
    public Kind getKind() {
        return Kind.CONTEXT_CONSTANT;
    }
}
