package solver.labels;

public record ValueOperand(Object value) implements Operand {

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
}
