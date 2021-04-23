package sql;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.type.SqlTypeName;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class DesugarOuterJoin {
    public static ParserResult perform(ParserResult result) {
        SqlSelect select;
        switch (result.getKind()) {
            case SELECT:
                select = (SqlSelect) result.getSqlNode();
                break;
            case ORDER_BY:
                select = (SqlSelect) ((SqlOrderBy) result.getSqlNode()).query;
                break;
            default:
                return result;
        }

        if (!select.isDistinct() || select.getGroup() != null || select.getHaving() != null
                || !select.getWindowList().getList().isEmpty()) { return result; }

        SqlNode fromClause = select.getFrom();
        if (fromClause.getKind() != SqlKind.JOIN) { return result; }
        SqlJoin join = (SqlJoin) fromClause;
        if (join.isNatural() || join.getJoinType() != JoinType.LEFT || join.getLeft().getKind() != SqlKind.IDENTIFIER
                || join.getRight().getKind() != SqlKind.IDENTIFIER
                || join.getConditionType() != JoinConditionType.ON) { return result; }
        SqlIdentifier joinLeft = (SqlIdentifier) join.getLeft();
        if (joinLeft.names.size() != 1) { return result; }
        String tableName = joinLeft.names.get(0);

        SqlIdentifier joinRight = (SqlIdentifier) join.getRight();
        if (joinRight.names.size() != 1) { return result; }
        String rightTableName = joinRight.names.get(0);

        SqlNode joinCondition = join.getCondition();
        if (replaceFieldsWithNull(joinCondition, rightTableName).isPresent()) {
            // We expect the join condition to be NULL if there is no match in the right table.
            return result;
        }

        List<SqlNode> selectList = select.getSelectList().getList();
        if (selectList.size() != 1) { return result; }
        SqlNode selectColumnNode = selectList.get(0);
        if (selectColumnNode.getKind() != SqlKind.IDENTIFIER) { return result; }
        SqlIdentifier selectId = (SqlIdentifier) selectColumnNode;
        if (selectId.names.size() != 2 || !selectId.names.get(0).equals(tableName)
                || !selectId.names.get(1).isEmpty()) { return result; }

        // Turn into a union.
        // RHS: inner join.
        SqlJoin rhsJoin = new SqlJoin(join.getParserPosition(), joinLeft, join.isNaturalNode(),
                SqlLiteral.createSymbol(JoinType.INNER, join.getJoinTypeNode().getParserPosition()),
                joinRight, join.getConditionTypeNode(), join.getCondition());
        SqlSelect rhs = new SqlSelect(select.getParserPosition(), SqlNodeList.EMPTY, select.getSelectList(), rhsJoin,
                select.getWhere(), select.getGroup(), select.getHaving(), select.getWindowList(), select.getOrderList(),
                select.getOffset(), select.getFetch(), select.getHints());

        // LHS: get rid of the join, substitute rightTable.columns with NULL in where clause.
        SqlNode newWhere = replaceFieldsWithNull(select.getWhere(), rightTableName).orElseGet(
                () -> SqlLiteral.createBoolean(false, select.getWhere().getParserPosition())
        );
        SqlSelect lhs = new SqlSelect(select.getParserPosition(), SqlNodeList.EMPTY, select.getSelectList(),
                joinRight, newWhere, select.getGroup(), select.getHaving(), select.getWindowList(),
                select.getOrderList(), select.getOffset(), select.getFetch(), select.getHints());

        SqlNode union = new SqlBasicCall(SqlStdOperatorTable.UNION, new SqlNode[]{lhs, rhs},
                select.getParserPosition());
        return new ParserResult(union.toString(), union.getKind(), union, false, false) {};
    }

    /**
     * Returns predicate where fields from relation are substituted with null.
     * @return a predicate, or empty if the entire predicate becomes null.
     */
    private static Optional<SqlNode> replaceFieldsWithNull(SqlNode node, String relation) {
        switch (node.getKind()) {
            case LITERAL:
                SqlLiteral lit = (SqlLiteral) node;
                if (lit.getTypeName() == SqlTypeName.NULL) {
                    return Optional.empty();
                }
                return Optional.of(node);
            case IDENTIFIER:
                List<String> names = ((SqlIdentifier) node).names;
                if (names.size() != 2) {
                    throw new IllegalArgumentException("identifier not supported: " + node);
                }
                if (names.get(0).equalsIgnoreCase(relation)) {
                    return Optional.empty();
                }
                return Optional.of(node);
            case OTHER:
                SqlNodeList nl = (SqlNodeList) node;
                ArrayList<SqlNode> newChildren = new ArrayList<>();
                for (SqlNode child : nl.getList()) {
                    Optional<SqlNode> newChild = replaceFieldsWithNull(child, relation);
                    if (!newChild.isPresent()) {
                        return Optional.empty();
                    }
                    newChildren.add(newChild.get());
                }
                return Optional.of(new SqlNodeList(newChildren, node.getParserPosition()));
        }

        SqlBasicCall call = (SqlBasicCall) node;
        SqlKind opKind = call.getOperator().getKind();
        if (opKind == SqlKind.NOT) {
            throw new IllegalArgumentException("not supported: NOT");
        }

        if (opKind == SqlKind.AND || opKind == SqlKind.OR) {
            Optional<SqlNode> newLeft = replaceFieldsWithNull(call.operand(0), relation);
            Optional<SqlNode> newRight = replaceFieldsWithNull(call.operand(1), relation);

            if (opKind == SqlKind.AND) {
                if (!newLeft.isPresent() || !newRight.isPresent()) {
                    return Optional.empty();
                }
            } else { // OR
                if (!newLeft.isPresent()) { return newRight; }
                if (!newRight.isPresent()) { return newLeft; }
            }

            return Optional.of(new SqlBasicCall(call.getOperator(), new SqlNode[]{newLeft.get(), newRight.get()},
                    call.getParserPosition()));
        }

        SqlNode[] operands = call.operands;
        SqlNode[] newOperands = new SqlNode[operands.length];
        for (int i = 0; i < operands.length; ++i) {
            Optional<SqlNode> curr = replaceFieldsWithNull(operands[i], relation);
            if (!curr.isPresent()) { // If an operand is NULL, the entire expression is NULL.
                return Optional.empty();
            }
            newOperands[i] = curr.get();
        }

        return Optional.of(new SqlBasicCall(call.getOperator(), newOperands, call.getParserPosition()));
    }
}
