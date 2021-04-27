package sql.preprocess;

import org.apache.calcite.sql.*;
import sql.ParserResult;

import java.util.List;

public class ExtractParams extends SqlTransformer {
    /**
     * Extracts literals in SQL query into parameters.
     * @param pr the SQL query.
     * @param params list of existing parameters; to be mutated.
     * @param paramNames list of existing parameter names; to be mutated.
     * @return new SQL query.
     */
    public static ParserResult perform(ParserResult pr, List<Object> params, List<String> paramNames) {
        SqlNode newNode = pr.getSqlNode().accept(new ExtractParams(params, paramNames));
        return new ParserResult(newNode.toString(), newNode.getKind(), newNode, false, false) {};
    }

    private final List<Object> params;
    private final List<String> paramNames;
    private int i = 0;

    private ExtractParams(List<Object> params, List<String> paramNames) {
        this.params = params;
        this.paramNames = paramNames;
    }

    @Override
    public SqlNode visit(SqlLiteral sqlLiteral) {
        Object v;
        switch (sqlLiteral.getTypeName()) {
            case BOOLEAN:
                v = sqlLiteral.booleanValue();
                break;
            case INTEGER:
            case DECIMAL:
                v = sqlLiteral.intValue(true);
                break;
            case CHAR:
                v = sqlLiteral.getValueAs(String.class);
                break;
            case SYMBOL:
                return sqlLiteral;
            default:
                throw new RuntimeException("unhandled literal type: " + sqlLiteral.getTypeName());
        }

        params.add(i, v);
        paramNames.add(i, "?");
        i += 1;
        return new SqlDynamicParam(i - 1, sqlLiteral.getParserPosition());
    }

    @Override
    public SqlNode visit(SqlDynamicParam sqlDynamicParam) {
        i += 1;
        if (sqlDynamicParam.getIndex() == i - 1) {
            return sqlDynamicParam;
        }
        return new SqlDynamicParam(i - 1, sqlDynamicParam.getParserPosition());
    }

    @Override
    public SqlNode visit(SqlCall sqlCall) {
        switch (sqlCall.getKind()) {
            case SELECT:
                SqlSelect newSelect = (SqlSelect) sqlCall.clone(sqlCall.getParserPosition());
                newSelect.setFrom(newSelect.getFrom().accept(this));
                SqlNode where = newSelect.getWhere();
                if (where != null) {
                    newSelect.setWhere(where.accept(this));
                }
                return newSelect;
            case JOIN:
                SqlJoin join = (SqlJoin) sqlCall;
                SqlNode newLeft = join.getLeft().accept(this);
                SqlNode newRight = join.getRight().accept(this);
                return new SqlJoin(join.getParserPosition(), newLeft, join.isNaturalNode(), join.getJoinTypeNode(),
                        newRight, join.getConditionTypeNode(), join.getCondition().accept(this));
        }

        return super.visit(sqlCall);
    }
}
