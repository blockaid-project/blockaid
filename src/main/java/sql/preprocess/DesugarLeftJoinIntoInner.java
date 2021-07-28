package sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import sql.ParserResult;
import sql.PrivacyQuery;
import sql.PrivacyQueryFactory;
import sql.SchemaPlusWithKey;

import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Turns left join into inner join in the trivial case where the join condition is on a foreign key.
 */
public class DesugarLeftJoinIntoInner implements Preprocessor {
    public static final DesugarLeftJoinIntoInner INSTANCE = new DesugarLeftJoinIntoInner();

    private DesugarLeftJoinIntoInner() {}

    @Override
    public Optional<PrivacyQuery> perform(ParserResult result, SchemaPlusWithKey schema, Object[] parameters,
                                          List<String> paramNames) {
        if (result.getKind() != SqlKind.SELECT) {
            return Optional.empty();
        }

        SqlSelect select = (SqlSelect) result.getSqlNode();
        if (select.getGroup() != null || select.getHaving() != null || !select.getWindowList().getList().isEmpty()) {
            return Optional.empty();
        }

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

        if (join.getCondition().getKind() != SqlKind.EQUALS) { return Optional.empty(); }
        SqlNode[] operands = ((SqlBasicCall) join.getCondition()).getOperands();

        if (operands[0].getKind() != SqlKind.IDENTIFIER) { return Optional.empty(); }
        SqlIdentifier eqLeft = (SqlIdentifier) operands[0];
        if (eqLeft.names.size() != 2) { return Optional.empty(); }
        if (operands[1].getKind() != SqlKind.IDENTIFIER) { return Optional.empty(); }
        SqlIdentifier eqRight = (SqlIdentifier) operands[1];
        if (eqRight.names.size() != 2) { return Optional.empty(); }

        if (eqLeft.names.get(0).equals(rightTableName)) {
            SqlIdentifier temp = eqLeft;
            eqLeft = eqRight;
            eqRight = temp;
        }

        if (!eqLeft.names.get(0).equals(tableName) || !eqRight.names.get(0).equals(rightTableName)) {
            return Optional.empty();
        }

        if (!schema.hasForeignKeyConstraint(eqLeft.names.get(0), eqLeft.names.get(1),
                eqRight.names.get(0), eqRight.names.get(1))) {
            return Optional.empty();
        }

        SqlJoin newJoin = new SqlJoin(join.getParserPosition(), joinLeft, join.isNaturalNode(),
                SqlLiteral.createSymbol(JoinType.INNER, join.getJoinTypeNode().getParserPosition()),
                joinRight, join.getConditionTypeNode(), join.getCondition());
        SqlSelect newSelect = (SqlSelect) select.clone(select.getParserPosition());
        newSelect.setFrom(newJoin);

        ParserResult newPR = new ParserResult(newSelect.toString(), newSelect.getKind(), newSelect, false,
                false) {};
        return Optional.of(PrivacyQueryFactory.createPrivacyQuery(newPR, schema, parameters, paramNames));
    }
}
