package sql.preprocess;

import com.google.common.collect.ImmutableList;
import org.apache.calcite.sql.*;
import sql.ParserResult;
import sql.PrivacyQuery;
import sql.PrivacyQueryFactory;
import sql.SchemaPlusWithKey;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * Converts:
 *     SELECT COUNT(*) FROM table WHERE...
 * into:
 *     SELECT pk1, pk2, ... FROM table WHERE...
 */
public class StripCountStar implements Preprocessor {
    public static final StripCountStar INSTANCE = new StripCountStar();

    private StripCountStar() {}


    public Optional<PrivacyQuery> perform(ParserResult result, SchemaPlusWithKey schema, List<Object> parameters,
                                          List<String> paramNames) {
        if (result.getKind() != SqlKind.SELECT) { return Optional.empty(); }

        SqlSelect sqlSelect = (SqlSelect) result.getSqlNode();
        SqlNode fromClause = sqlSelect.getFrom();
        if (fromClause.getKind() != SqlKind.IDENTIFIER) { return Optional.empty(); }
        SqlIdentifier fromId = (SqlIdentifier) fromClause;
        if (fromId.names.size() != 1) { return Optional.empty(); }

        String tableName = fromId.names.get(0);
        Optional<ImmutableList<String>> oPkColumns = schema.getPrimaryKeyColumns(tableName);
        if (oPkColumns.isEmpty()) { return Optional.empty(); }
        ImmutableList<String> pkColumns = oPkColumns.get();

        SqlNodeList l = sqlSelect.getSelectList();
        if (l.size() != 1) { return Optional.empty(); }

        SqlNode node = l.get(0);
        if (!(node instanceof SqlBasicCall)) { return Optional.empty(); }

        SqlBasicCall call = (SqlBasicCall) node;
        if (!call.getOperator().getName().equals("COUNT")) { return Optional.empty(); }
        SqlNode operand = call.getOperands()[0];
        if (operand.getKind() != SqlKind.IDENTIFIER) { return Optional.empty(); }
        SqlIdentifier opId = (SqlIdentifier) operand;
        if (!opId.isStar()) { return Optional.empty(); }

        SqlSelect newSelect = (SqlSelect) sqlSelect.clone(sqlSelect.getParserPosition());

        List<SqlNode> newSelectList = new ArrayList<>();
        for (String col : pkColumns) {
            newSelectList.add(new SqlIdentifier(col, node.getParserPosition()));
        }
        newSelect.setSelectList(new SqlNodeList(newSelectList, l.getParserPosition()));

        ParserResult newPR = new ParserResult(newSelect);
        PrivacyQuery pq = new PrivacyQueryEmptyRBWrapper(
                PrivacyQueryFactory.createPrivacyQuery(newPR, schema, parameters, paramNames));
        return Optional.of(pq);
    }
}
