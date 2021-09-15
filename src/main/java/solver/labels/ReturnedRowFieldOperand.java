package solver.labels;

import java.util.Objects;

public record ReturnedRowFieldOperand(int queryIdx, int returnedRowIdx, int colIdx) implements Operand {
    @Override
    public Kind getKind() {
        return Kind.RETURNED_ROW_ATTR;
    }

    @Override
    public String toString() {
        return "ReturnedRowFieldOperand_" + queryIdx + "_" + returnedRowIdx + "_" + colIdx;
    }
}
