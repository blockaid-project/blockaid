package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

public record ContextConstantOperand(String name) implements Operand {
    @Override
    public String toString() {
        return "ContextConstantOperand_" + name;
    }

    @Override
    public Kind getKind() {
        return Kind.CONTEXT_CONSTANT;
    }
}
