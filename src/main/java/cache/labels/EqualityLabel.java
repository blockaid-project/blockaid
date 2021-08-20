package cache.labels;

import java.util.Objects;

import static com.google.common.base.Preconditions.checkNotNull;

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

    public interface Operand {
        enum Kind {
            CONTEXT_CONSTANT,
            QUERY_PARAM,
            RETURNED_ROW_FIELD,
            VALUE,
        }

        Kind getKind();
    }

    public static class QueryParamOperand implements Operand {
        private final int queryIdx;
        private final boolean isCurrentQuery;
        private final int paramIdx;

        public QueryParamOperand(int queryIdx, boolean isCurrentQuery, int paramIdx) {
            this.queryIdx = queryIdx;
            this.isCurrentQuery = isCurrentQuery;
            this.paramIdx = paramIdx;
        }

        public int getQueryIdx() {
            return queryIdx;
        }

        public int getParamIdx() {
            return paramIdx;
        }

        public boolean isCurrentQuery() {
            return isCurrentQuery;
        }

        @Override
        public Kind getKind() {
            return Kind.QUERY_PARAM;
        }

        @Override
        public String toString() {
            return "QueryParamOperand_" + (isCurrentQuery ? "curr" : queryIdx) + "_" + paramIdx;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            QueryParamOperand that = (QueryParamOperand) o;
            return queryIdx == that.queryIdx && isCurrentQuery == that.isCurrentQuery && paramIdx == that.paramIdx;
        }

        @Override
        public int hashCode() {
            return Objects.hash(queryIdx, isCurrentQuery, paramIdx);
        }
    }

    public static class ReturnedRowFieldOperand implements Operand {
        private final int queryIdx;
        private final boolean isCurrentQuery;
        private final int returnedRowIdx;
        private final int colIdx;

        public ReturnedRowFieldOperand(int queryIdx, boolean isCurrentQuery, int returnedRowIdx, int colIdx) {
            this.queryIdx = queryIdx;
            this.isCurrentQuery = isCurrentQuery;
            this.returnedRowIdx = returnedRowIdx;
            this.colIdx = colIdx;
        }

        public int getQueryIdx() {
            return queryIdx;
        }

        public boolean isCurrentQuery() {
            return isCurrentQuery;
        }

        public int getReturnedRowIdx() {
            return returnedRowIdx;
        }

        public int getColIdx() {
            return colIdx;
        }

        @Override
        public Kind getKind() {
            return Kind.RETURNED_ROW_FIELD;
        }

        @Override
        public String toString() {
            return "ReturnedRowFieldOperand_" + (isCurrentQuery ? "curr" : queryIdx) + "_" + returnedRowIdx + "_" + colIdx;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            ReturnedRowFieldOperand that = (ReturnedRowFieldOperand) o;
            return queryIdx == that.queryIdx && isCurrentQuery == that.isCurrentQuery && returnedRowIdx == that.returnedRowIdx && colIdx == that.colIdx;
        }

        @Override
        public int hashCode() {
            return Objects.hash(queryIdx, isCurrentQuery, returnedRowIdx, colIdx);
        }
    }

    public static class ValueOperand implements Operand {
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

    public static class ContextConstantOperand implements Operand {
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
}
