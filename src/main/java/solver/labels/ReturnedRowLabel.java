package solver.labels;

import java.util.Collection;
import java.util.Collections;
import java.util.Objects;

public record ReturnedRowLabel(int queryIdx, int rowIdx) implements Label {
    @Override
    public Kind getKind() {
        return Kind.RETURNED_ROW;
    }

    @Override
    public Collection<Operand> getOperands() {
        return Collections.emptyList();
    }

    @Override
    public String toString() {
        return "ReturnedRowLabel!" + queryIdx + "!" + rowIdx;
    }
}
