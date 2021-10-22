package edu.berkeley.cs.netsys.privacy_proxy.sql.preprocess;

import org.apache.calcite.sql.*;
import edu.berkeley.cs.netsys.privacy_proxy.sql.ParserResult;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQueryFactory;
import edu.berkeley.cs.netsys.privacy_proxy.sql.SchemaPlusWithKey;
import edu.berkeley.cs.netsys.privacy_proxy.util.SqlNodes;

import java.util.List;
import java.util.Optional;

import static edu.berkeley.cs.netsys.privacy_proxy.sql.preprocess.Util.getTableName;

/**
 * Turns left join into inner join in the trivial case where the join condition is on a foreign key.
 */
public class DesugarLeftJoinIntoInner implements Preprocessor {
    public static final DesugarLeftJoinIntoInner INSTANCE = new DesugarLeftJoinIntoInner();

    private DesugarLeftJoinIntoInner() {}

    @Override
    public Optional<PrivacyQuery> perform(ParserResult result, SchemaPlusWithKey schema, List<Object> parameters,
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
        if (join.isNatural() || join.getJoinType() != JoinType.LEFT || join.getConditionType() != JoinConditionType.ON) {
            return Optional.empty();
        }

        SqlNode joinLeft = join.getLeft(), joinRight = join.getRight();
        String tableName, rightTableName;
        {
            Optional<String> oTableName = getTableName(joinLeft), oRightTableName = getTableName(joinRight);
            if (oTableName.isEmpty() || oRightTableName.isEmpty()) {
                return Optional.empty();
            }
            tableName = oTableName.get();
            rightTableName = oRightTableName.get();
        }

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
        SqlSelect newSelect = SqlNodes.shallowCopy(select);
        newSelect.setFrom(newJoin);

        ParserResult newPR = new ParserResult(newSelect);
        return Optional.of(PrivacyQueryFactory.createPrivacyQuery(newPR, schema, parameters, paramNames));
    }
}
