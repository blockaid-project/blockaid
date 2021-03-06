package edu.berkeley.cs.netsys.privacy_proxy.sql.preprocess;

import org.apache.calcite.sql.*;
import edu.berkeley.cs.netsys.privacy_proxy.sql.ParserResult;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQueryFactory;
import edu.berkeley.cs.netsys.privacy_proxy.sql.SchemaPlusWithKey;

import java.util.List;
import java.util.Optional;

public class StripUnaryOpSubquery implements Preprocessor {
    public static final StripUnaryOpSubquery INSTANCE = new StripUnaryOpSubquery();

    private StripUnaryOpSubquery() {}

    public Optional<PrivacyQuery> perform(ParserResult result, SchemaPlusWithKey schema, List<Object> parameters,
                                          List<String> paramNames) {
        if (result.getKind() != SqlKind.SELECT) {
            return Optional.empty();
        }

        SqlSelect sqlSelect = (SqlSelect) result.getSqlNode();
        SqlNode fromClause = sqlSelect.getFrom();
        boolean stripped = false;
        while (fromClause.getKind() == SqlKind.AS && (
                ((SqlBasicCall) fromClause).operand(0) instanceof SqlSelect
                        || ((SqlBasicCall) fromClause).operand(0) instanceof SqlOrderBy)) {
            if (((SqlBasicCall) fromClause).operand(0) instanceof SqlOrderBy) {
                sqlSelect = (SqlSelect) ((SqlOrderBy) ((SqlBasicCall) fromClause).operand(0)).query;
            } else {
                sqlSelect = ((SqlBasicCall) fromClause).operand(0);
            }
            fromClause = sqlSelect.getFrom();
            stripped = true;
        }

        if (!stripped) {
            return Optional.empty();
        }

        // Only handling the case where this stripping doesn't remove any parameters.
        if (sqlSelect.accept(DynParamCounter.INSTANCE) != parameters.size()) {
            return Optional.empty();
        }

        ParserResult newPR = new ParserResult(sqlSelect);
        // After stripping, need to set result bitmap to empty so that the results of this query are not processed.
        PrivacyQuery pq = new PrivacyQueryEmptyRBWrapper(
                PrivacyQueryFactory.createPrivacyQuery(newPR, schema, parameters, paramNames));
        return Optional.of(pq);
    }
}
