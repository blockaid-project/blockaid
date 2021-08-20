package cache.labels;

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
    public String toString() {
        return "ReturnedRowLabel!" + queryIdx + "!" + rowIdx;
    }
}
