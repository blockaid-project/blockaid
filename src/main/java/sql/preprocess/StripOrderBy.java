package sql.preprocess;

import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.SqlOrderBy;
import sql.ParserResult;
import sql.PrivacyQuery;
import sql.PrivacyQueryFactory;
import sql.SchemaPlusWithKey;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public class StripOrderBy implements Preprocessor {
    public static final StripOrderBy INSTANCE = new StripOrderBy();

    private StripOrderBy() {}

    public Optional<PrivacyQuery> perform(ParserResult result, SchemaPlusWithKey schema, Object[] parameters,
                                          List<String> paramNames, Map<Long, String> revConstMap) {
        if (result.getKind() != SqlKind.ORDER_BY) {
            return Optional.empty();
        }

        SqlOrderBy ob = (SqlOrderBy) result.getSqlNode();
        SqlNode subQuery = ob.query;
        ParserResult newPR = new ParserResult(subQuery.toString(), subQuery.getKind(), subQuery, false, false) {};

        // We might have removed some parameters in the query.  Remove them in `parameters` and `paramNames`, too.
        int numParamsInSubQuery = subQuery.accept(DynParamCounter.INSTANCE);
        if (numParamsInSubQuery != parameters.length) {
            // Assuming the removed parameters are at the end of the list.  This is correct?
            parameters = Arrays.stream(parameters).limit(numParamsInSubQuery).collect(Collectors.toList())
                    .toArray(new Object[numParamsInSubQuery]);
            paramNames = paramNames.stream().limit(numParamsInSubQuery).collect(Collectors.toList());
        }

        return Optional.of(PrivacyQueryFactory.createPrivacyQuery(newPR, schema, parameters, paramNames, revConstMap));
    }
}
