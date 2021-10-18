package sql;

import org.apache.calcite.sql.*;
import org.apache.calcite.util.Litmus;

import java.util.List;
import java.util.Objects;

import static com.google.common.base.Preconditions.*;

/**
 * Wrapper around `SqlNode` that (1) has `equals` and `hashCode` defined and (2) caches the node's string repr.
 * Assumes that the `SqlNode` does not change.
 */
public class ParserResult {
    private final SqlNode sqlNode;

    // Lazily computed.
    private Integer cachedHashCode = null;

    private String parsedSql = null;
    // Lazily computed (`node.toString` can take a while).  Use `getParsedSql()` to access.

    public ParserResult(SqlNode sqlNode) {
        this.sqlNode = checkNotNull(sqlNode);
    }

    public String getParsedSql() {
        if (parsedSql == null) {
            parsedSql = sqlNode.toString().replace("\n", " ");
        }
        return parsedSql;
    }

    public SqlKind getKind() {
        return sqlNode.getKind();
    }

    public SqlNode getSqlNode() {
        return sqlNode;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ParserResult that = (ParserResult) o;
        return sqlNode.equalsDeep(that.sqlNode, Litmus.IGNORE);
    }

    @Override
    public int hashCode() {
        if (cachedHashCode == null) {
            cachedHashCode = computeHashCode(sqlNode);
        }
        return cachedHashCode;
    }

    private static int computeHashCode(SqlNode node) {
        if (node == null) {
            return 0;
        } else if (node instanceof SqlDynamicParam param) {
            return Objects.hash(SqlKind.DYNAMIC_PARAM, param.getIndex());
        } else if (node instanceof SqlLiteral lit) {
            return Objects.hash(SqlKind.LITERAL, lit.getValue());
        } else if (node instanceof SqlIdentifier identifier) {
            checkArgument(identifier.getCollation() == null, "unsupported: identifier collation");
            return Objects.hash(SqlKind.IDENTIFIER, identifier.names);
        } else if (node instanceof SqlCall call) {
            // `SqlWindow` is treated specially by `equalsDeep`.  We don't handle it for now.
            checkArgument(!(call instanceof SqlWindow), "unsupported: SqlWindow");
            int ret = call.getKind().hashCode();
            ret = 31 * ret + computeHashCode(call.getOperandList());
            // Case-insensitive like in `equalsDeep`.
            ret = 31 * ret + call.getOperator().getName().toLowerCase().hashCode();
            SqlLiteral quantifier = call.getFunctionQuantifier();
            ret = 31 * ret + (quantifier == null ? 0 : Objects.hashCode(quantifier.getValue()));
            return ret;
        } else if (node instanceof SqlNodeList nodeList) {
            return computeHashCode(nodeList.getList());
        } else {
            throw new UnsupportedOperationException("unhandled node type: " + node.getClass().getName());
        }
    }

    private static int computeHashCode(List<SqlNode> nodes) {
        int hashCode = 0;
        for (SqlNode e : nodes) {
            // TODO(zhangwen): each element is a sub-tree; is this a good hash function?
            hashCode = 31 * hashCode + computeHashCode(e);
        }
        return hashCode;
    }

    @Override
    public String toString() {
        return getParsedSql();
    }
}