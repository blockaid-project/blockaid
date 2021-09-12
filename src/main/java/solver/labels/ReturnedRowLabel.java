package solver.labels;

import java.util.Collection;
import java.util.Collections;
import java.util.Objects;

public class ReturnedRowLabel implements Label {
    private final int queryIdx;
    private final int rowIdx;

    public ReturnedRowLabel(int queryIdx, int rowIdx) {
        this.queryIdx = queryIdx;
        this.rowIdx = rowIdx;
    }

    public int getQueryIdx() {
        return queryIdx;
    }

    public int getRowIdx() {
        return rowIdx;
    }

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

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ReturnedRowLabel that = (ReturnedRowLabel) o;
        return queryIdx == that.queryIdx && rowIdx == that.rowIdx;
    }

    @Override
    public int hashCode() {
        return Objects.hash(queryIdx, rowIdx);
    }
}
