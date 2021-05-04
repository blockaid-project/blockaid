package sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.type.SqlTypeName;
import sql.*;

import java.util.*;

public class DesugarLeftJoinIntoUnion implements Preprocessor {
    public static final DesugarLeftJoinIntoUnion INSTANCE = new DesugarLeftJoinIntoUnion();

    private DesugarLeftJoinIntoUnion() {}

    public Optional<PrivacyQuery> perform(ParserResult result, SchemaPlusWithKey schema, Object[] parameters,
                                          List<String> paramNames, Map<Integer, String> revConstMap) {
        if (result.getKind() != SqlKind.SELECT) {
            return Optional.empty();
        }

        SqlSelect select = (SqlSelect) result.getSqlNode();
        if (!select.isDistinct() || select.getGroup() != null || select.getHaving() != null
                || !select.getWindowList().getList().isEmpty()) { return Optional.empty(); }

        SqlNode fromClause = select.getFrom();
        if (fromClause.getKind() != SqlKind.JOIN) { return Optional.empty(); }
        SqlJoin join = (SqlJoin) fromClause;
        if (join.isNatural() || join.getJoinType() != JoinType.LEFT || join.getLeft().getKind() != SqlKind.IDENTIFIER
                || join.getRight().getKind() != SqlKind.IDENTIFIER
                || join.getConditionType() != JoinConditionType.ON) { return Optional.empty(); }
        SqlIdentifier joinLeft = (SqlIdentifier) join.getLeft();
        if (joinLeft.names.size() != 1) { return Optional.empty(); }
        String tableName = joinLeft.names.get(0);

        SqlIdentifier joinRight = (SqlIdentifier) join.getRight();
        if (joinRight.names.size() != 1) { return Optional.empty(); }
        String rightTableName = joinRight.names.get(0);

        SqlNode joinCondition = join.getCondition();
        if (replaceFieldsWithNull(joinCondition, rightTableName).isPresent()) {
            // We expect the join condition to be NULL if there is no match in the right table.
            return Optional.empty();
        }

        List<SqlNode> selectList = select.getSelectList().getList();
        if (selectList.size() != 1) { return Optional.empty(); }
        SqlNode selectColumnNode = selectList.get(0);
        if (selectColumnNode.getKind() != SqlKind.IDENTIFIER) { return Optional.empty(); }
        SqlIdentifier selectId = (SqlIdentifier) selectColumnNode;
        if (selectId.names.size() != 2 || !selectId.names.get(0).equals(tableName)) { return Optional.empty(); }

        // Only handling the case where the select list contains no parameters.
        if (select.getSelectList().accept(DynParamCounter.INSTANCE) > 0) {
            return Optional.empty();
        }

        // Turn into a union.
        // LHS: simply change "outer join" into "inner join".
        SqlJoin lhsJoin = new SqlJoin(join.getParserPosition(), joinLeft, join.isNaturalNode(),
                SqlLiteral.createSymbol(JoinType.INNER, join.getJoinTypeNode().getParserPosition()),
                joinRight, join.getConditionTypeNode(), join.getCondition());
        SqlSelect lhs = new SqlSelect(select.getParserPosition(), SqlNodeList.EMPTY, select.getSelectList(), lhsJoin,
                select.getWhere(), select.getGroup(), select.getHaving(), select.getWindowList(), select.getOrderList(),
                select.getOffset(), select.getFetch(), select.getHints());

        // RHS: get rid of the join, substitute rightTable.columns with NULL in where clause.
        SqlNode newWhere = replaceFieldsWithNull(select.getWhere(), rightTableName)
                .orElseGet(() -> SqlLiteral.createBoolean(false, select.getWhere().getParserPosition())
        );
        SqlNode rhs = new SqlSelect(select.getParserPosition(), SqlNodeList.EMPTY, select.getSelectList(),
                joinLeft, newWhere, select.getGroup(), select.getHaving(), select.getWindowList(),
                select.getOrderList(), select.getOffset(), select.getFetch(), select.getHints());

        RenumberDynParams r = new RenumberDynParams(parameters.length);
        rhs = rhs.accept(r);

        SqlNode union = new SqlBasicCall(SqlStdOperatorTable.UNION, new SqlNode[]{lhs, rhs},
                select.getParserPosition());
        ParserResult newPR = new ParserResult(union.toString(), union.getKind(), union, false, false) {};

        List<SqlDynamicParam> renumberedParams = r.getRenumberedParams();
        Object[] newParameters = new Object[parameters.length + renumberedParams.size()];
        System.arraycopy(parameters, 0, newParameters, 0, parameters.length);
        ArrayList<String> newParamNames = new ArrayList<>(paramNames);

        for (int i = 0; i < renumberedParams.size(); ++i) {
            int oldIndex = renumberedParams.get(i).getIndex();
            newParameters[parameters.length + i] = parameters[oldIndex];
            newParamNames.add(paramNames.get(oldIndex));
        }

        return Optional.of(PrivacyQueryFactory.createPrivacyQuery(newPR, schema, newParameters, newParamNames, revConstMap));
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
            case DYNAMIC_PARAM:
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

    private static class RenumberDynParams extends SqlTransformer {
        private final int startIndex;
        private int numParamsSoFar = 0;
        private final List<SqlDynamicParam> renumberedParams = new ArrayList<>();

        public List<SqlDynamicParam> getRenumberedParams() {
            return Collections.unmodifiableList(renumberedParams);
        }

        public RenumberDynParams(int startIndex) {
            this.startIndex = startIndex;
        }

        @Override
        public SqlNode visit(SqlDynamicParam sqlDynamicParam) {
            renumberedParams.add(sqlDynamicParam);
            SqlDynamicParam np = new SqlDynamicParam(startIndex + numParamsSoFar,
                    sqlDynamicParam.getParserPosition());
            numParamsSoFar += 1;
            return np;
        }
    }
}
