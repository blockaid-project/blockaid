package sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.util.SqlVisitor;

/**
 * Counts the number of dynamic parameters in a SQL node.
 */
class DynParamCounter implements SqlVisitor<Integer> {
    public static final DynParamCounter INSTANCE = new DynParamCounter();

    private DynParamCounter() {}

    @Override
    public Integer visit(SqlLiteral sqlLiteral) {
        return 0;
    }

    @Override
    public Integer visit(SqlCall sqlCall) {
        int total = 0;
        for (SqlNode sn : sqlCall.getOperandList()) {
            if (sn != null) {
                total += sn.accept(this);
            }
        }
        return total;
    }

    @Override
    public Integer visit(SqlNodeList sqlNodeList) {
        int total = 0;
        for (SqlNode sn : sqlNodeList) {
            total += sn.accept(this);
        }
        return total;
    }

    @Override
    public Integer visit(SqlIdentifier sqlIdentifier) {
        return 0;
    }

    @Override
    public Integer visit(SqlDataTypeSpec sqlDataTypeSpec) {
        throw new RuntimeException("not supported: SqlDataTypeSpec");
    }

    @Override
    public Integer visit(SqlDynamicParam sqlDynamicParam) {
        return 1;
    }

    @Override
    public Integer visit(SqlIntervalQualifier sqlIntervalQualifier) {
        throw new RuntimeException("not supported: SqlIntervalQualifier");
    }
}
