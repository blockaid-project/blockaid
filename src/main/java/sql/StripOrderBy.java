package sql;

import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlOrderBy;
import org.apache.calcite.sql.SqlSelect;

import java.util.List;
import java.util.Optional;

public class StripOrderBy {
    public static Optional<PrivacyQuery> perform(ParserResult result, SchemaPlusWithKey schema, Object[] parameters,
                                                 List<String> paramNames) {
        if (result.getKind() != SqlKind.ORDER_BY) {
            return Optional.empty();
        }

        SqlSelect select = (SqlSelect) ((SqlOrderBy) result.getSqlNode()).query;
        ParserResult newPR = new ParserResult(select.toString(), select.getKind(), select, false, false) {};
        return Optional.of(PrivacyQueryFactory.createPrivacyQuery(newPR, schema, parameters, paramNames));
    }
}
