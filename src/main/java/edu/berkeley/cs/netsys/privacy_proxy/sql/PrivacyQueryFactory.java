package edu.berkeley.cs.netsys.privacy_proxy.sql;

import edu.berkeley.cs.netsys.privacy_proxy.sql.preprocess.*;

import java.util.*;

public class PrivacyQueryFactory {
    private static final Preprocessor[] preprocessors = {
            StripOrderBy.INSTANCE,
            StripUnaryOpSubquery.INSTANCE,
            DesugarLeftJoinIntoInner.INSTANCE,
            DesugarLeftJoinIntoUnion.INSTANCE,
            StripSum.INSTANCE,
            StripCountStar.INSTANCE,
    };

    public static PrivacyQuery createPrivacyQuery(ParserResult result, SchemaPlusWithKey schema,
                                                  List<Object> parameters, List<String> paramNames)
    {
        if (result == null) {
            return null;
        }

        for (Preprocessor p : preprocessors) {
            Optional<PrivacyQuery> res = p.perform(result, schema, parameters, paramNames);
            if (res.isPresent()) {
                return res.get();
            }
        }

        // Extract literals into query parameters.
        ArrayList<Object> newParams = new ArrayList<>(parameters);
        ArrayList<String> newParamNames = new ArrayList<>(paramNames);
        result = ExtractParams.perform(result, newParams, newParamNames);

        return switch (result.getKind()) {
            case SELECT, ORDER_BY -> new PrivacyQuerySelect(result, schema, newParams, newParamNames);
            case UNION -> new PrivacyQueryUnion(result, schema, newParams, newParamNames);
            default -> throw new AssertionError("unexpected");
        };
    }
}
