package sql;

import sql.preprocess.*;

import java.util.*;

public class PrivacyQueryFactory {

    public static PrivacyQuery createPrivacyQuery(ParserResult result, SchemaPlusWithKey schema)
    {
        return createPrivacyQuery(result, schema, new Object[0], Collections.emptyList());
    }

    private static final Preprocessor[] preprocessors = {
            StripOrderBy.INSTANCE,
            StripUnaryOpSubquery.INSTANCE,
            DesugarLeftJoinIntoInner.INSTANCE,
            DesugarLeftJoinIntoUnion.INSTANCE
    };

    public static PrivacyQuery createPrivacyQuery(ParserResult result, SchemaPlusWithKey schema, Object[] parameters,
                                                  List<String> paramNames)
    {
        if (result == null){
            return null;
        }

        for (Preprocessor p : preprocessors) {
            Optional<PrivacyQuery> res = p.perform(result, schema, parameters, paramNames);
            if (res.isPresent()) {
                return res.get();
            }
        }

        ArrayList<Object> newParams = new ArrayList<>(Arrays.asList(parameters));
        ArrayList<String> newParamNames = new ArrayList<>(paramNames);
        result = ExtractParams.perform(result, newParams, newParamNames);

        switch(result.getKind()) {
            case SELECT:
            case ORDER_BY:
                return new PrivacyQuerySelect(result, schema, newParams, newParamNames);
            case UNION:
                return new PrivacyQueryUnion(result, schema, newParams, newParamNames);
            default:
                throw new AssertionError("unexpected");
        }
    }
}
