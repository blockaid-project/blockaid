package edu.berkeley.cs.netsys.privacy_proxy.sql.preprocess;

import org.apache.calcite.sql.*;
import edu.berkeley.cs.netsys.privacy_proxy.sql.ParserResult;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQueryFactory;
import edu.berkeley.cs.netsys.privacy_proxy.sql.SchemaPlusWithKey;
import edu.berkeley.cs.netsys.privacy_proxy.util.SqlNodes;

import java.util.List;
import java.util.Optional;

public class StripSum implements Preprocessor {
    public static final StripSum INSTANCE = new StripSum();

    private StripSum() {}

    public Optional<PrivacyQuery> perform(ParserResult result, SchemaPlusWithKey schema, List<Object> parameters,
                                          List<String> paramNames) {
        if (result.getKind() != SqlKind.SELECT) { return Optional.empty(); }

        SqlSelect sqlSelect = (SqlSelect) result.getSqlNode();
        SqlNode fromClause = sqlSelect.getFrom();
        if (fromClause.getKind() != SqlKind.IDENTIFIER) { return Optional.empty(); }

        SqlNodeList l = sqlSelect.getSelectList();
        if (l.size() != 1) { return Optional.empty(); }

        SqlNode node = l.get(0);
        if (!(node instanceof SqlBasicCall call)) { return Optional.empty(); }

        if (!call.getOperator().getName().equals("SUM")) { return Optional.empty(); }
        SqlNode operand = call.getOperands()[0];
        if (operand.getKind() != SqlKind.IDENTIFIER) { return Optional.empty(); }
        SqlIdentifier opId = (SqlIdentifier) operand;
        if (opId.names.size() != 2) { return Optional.empty(); }

        SqlSelect newSelect = SqlNodes.shallowCopy(sqlSelect);
        newSelect.setSelectList(SqlNodeList.SINGLETON_STAR);
        ParserResult newPR = new ParserResult(newSelect);
        PrivacyQuery pq = new PrivacyQueryEmptyRBWrapper(
                PrivacyQueryFactory.createPrivacyQuery(newPR, schema, parameters, paramNames));
        return Optional.of(pq);
    }
}
