package sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.util.SqlVisitor;
import util.SqlNodes;

import java.util.ArrayList;
import java.util.List;

class SqlTransformer implements SqlVisitor<SqlNode> {

    @Override
    public SqlNode visit(SqlLiteral sqlLiteral) {
        return sqlLiteral;
    }

    @Override
    public SqlNode visit(SqlCall sqlCall) {
        SqlCall nc = SqlNodes.shallowCopy(sqlCall);

        List<SqlNode> operands = sqlCall.getOperandList();
        int numOperands = operands.size();
        if (sqlCall.getKind() == SqlKind.SELECT) {
            // FIXME(zhangwen): HACK-- a select node's `setOperand` method doesn't support setting the last operand, so we do that here.
            // This is fixed in https://github.com/apache/calcite/pull/2477, but the fix hasn't made it into a release.
            SqlNodeList newHints = null;
            SqlNodeList oldHints = ((SqlSelect) sqlCall).getHints();
            if (oldHints != null) {
                newHints = (SqlNodeList) oldHints.accept(this);
            }
            ((SqlSelect) nc).setHints(newHints);
            numOperands -= 1;
        }
        for (int i = 0; i < numOperands; ++i) {
            SqlNode o = operands.get(i);
            if (o != null) {
                nc.setOperand(i, o.accept(this));
            }
        }

        return nc;
    }

    @Override
    public SqlNode visit(SqlNodeList sqlNodeList) {
        ArrayList<SqlNode> l = new ArrayList<>();
        for (SqlNode n : sqlNodeList) {
            if (n == null) {
                l.add(null);
            } else {
                l.add(n.accept(this));
            }
        }
        return new SqlNodeList(l, sqlNodeList.getParserPosition());
    }

    @Override
    public SqlNode visit(SqlIdentifier sqlIdentifier) {
        return sqlIdentifier;
    }

    @Override
    public SqlNode visit(SqlDataTypeSpec sqlDataTypeSpec) {
        return sqlDataTypeSpec;
    }

    @Override
    public SqlNode visit(SqlDynamicParam sqlDynamicParam) {
        return sqlDynamicParam;
    }

    @Override
    public SqlNode visit(SqlIntervalQualifier sqlIntervalQualifier) {
        throw new RuntimeException("not supported: SqlIntervalQualifier");
    }
}
