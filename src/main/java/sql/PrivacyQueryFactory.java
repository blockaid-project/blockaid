package sql;

import sql.preprocess.*;

import java.util.*;

public class PrivacyQueryFactory {

    private static final Preprocessor[] preprocessors = {
            StripOrderBy.INSTANCE,
            StripUnaryOpSubquery.INSTANCE,
            DesugarLeftJoinIntoInner.INSTANCE,
            DesugarLeftJoinIntoUnion.INSTANCE
    };

    public static PrivacyQuery createPrivacyQuery(ParserResult result, SchemaPlusWithKey schema, Object[] parameters,
                                                  List<String> paramNames, Map<Integer, String> revConstMap)
    {
        if (result == null){
            return null;
        }

        for (Preprocessor p : preprocessors) {
            Optional<PrivacyQuery> res = p.perform(result, schema, parameters, paramNames, revConstMap);
            if (res.isPresent()) {
                return res.get();
            }
        }

        ArrayList<Object> newParams = new ArrayList<>(Arrays.asList(parameters));
        ArrayList<String> newParamNames = new ArrayList<>(paramNames);
        result = ExtractParams.perform(result, newParams, newParamNames);

        // FIXME(zhangwen): HACK-- for parameter values equal to a const in constMap, assign it the corresponding const name.
        String queryText = result.getParsedSql();
        StringBuilder sb = new StringBuilder(); // For building the new query string.
        for (int pi = 0, si = 0; pi < newParams.size(); ++pi) {
            // FIXME (zhangwen): HACK-- again, string substitution for '?' is not robust...
            int nextSi = queryText.indexOf("?", si) + 1;
            if (nextSi == 0) {
                throw new RuntimeException("parameter-text mismatch??");
            }
            sb.append(queryText, si, nextSi);
            si = nextSi;

            Object param = newParams.get(pi);
            if (param instanceof Integer && newParamNames.get(pi).equals("?")) {
                String name = revConstMap.get(param);
                if (name != null) {
                    newParamNames.set(pi, name);
                    sb.append(name);
                }
            }
        }
        result.setParsedSql(sb.toString());

        switch(result.getKind()) {
            case SELECT:
            case ORDER_BY:
                return new PrivacyQuerySelect(result, schema, newParams, newParamNames);
            case UNION:
                return new PrivacyQueryUnion(result, schema, newParams, newParamNames, revConstMap);
            default:
                throw new AssertionError("unexpected");
        }
    }
}
