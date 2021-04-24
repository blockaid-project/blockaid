package sql;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

public class PrivacyQueryFactory {

    public static PrivacyQuery createPrivacyQuery(ParserResult result, SchemaPlusWithKey schema)
    {
        return createPrivacyQuery(result, schema, new Object[0], Collections.emptyList());
    }

    public static PrivacyQuery createPrivacyQuery(ParserResult result, SchemaPlusWithKey schema, Object[] parameters, List<String> paramNames)
    {
        if (result == null){
            return null;
        }

        Optional<PrivacyQuery> res;
        if ((res = StripOrderBy.perform(result, schema, parameters, paramNames)).isPresent()) {
            return res.get();
        }
        if ((res = StripUnaryOpSubquery.perform(result, schema, parameters, paramNames)).isPresent()) {
            return res.get();
        }
        if ((res = DesugarOuterJoin.perform(result, schema, parameters, paramNames)).isPresent()) {
            return res.get();
        }

        switch(result.getKind()) {
            case SELECT:
            case ORDER_BY:
                return new PrivacyQuerySelect(result, schema, parameters, paramNames);
            case UNION:
                return new PrivacyQueryUnion(result, schema, parameters, paramNames);
            default:
                throw new AssertionError("unexpected");
        }
    }
}
