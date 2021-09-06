package cache.labels;

import java.util.Objects;

public class ReturnedRowFieldOperand implements Operand {
    private final int queryIdx;
    private final int returnedRowIdx;
    private final int colIdx;

    public ReturnedRowFieldOperand(int queryIdx, int returnedRowIdx, int colIdx) {
        this.queryIdx = queryIdx;
        this.returnedRowIdx = returnedRowIdx;
        this.colIdx = colIdx;
    }

    public int getQueryIdx() {
        return queryIdx;
    }

    public int getReturnedRowIdx() {
        return returnedRowIdx;
    }

    public int getColIdx() {
        return colIdx;
    }

    @Override
    public Kind getKind() {
        return Kind.RETURNED_ROW_ATTR;
    }

    @Override
    public String toString() {
        return "ReturnedRowFieldOperand_" + queryIdx + "_" + returnedRowIdx + "_" + colIdx;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ReturnedRowFieldOperand that = (ReturnedRowFieldOperand) o;
        return queryIdx == that.queryIdx && returnedRowIdx == that.returnedRowIdx && colIdx == that.colIdx;
    }

    @Override
    public int hashCode() {
        return Objects.hash(queryIdx, returnedRowIdx, colIdx);
    }
}

