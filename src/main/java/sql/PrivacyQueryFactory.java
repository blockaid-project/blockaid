package sql;

import sql.preprocess.*;

import java.time.LocalDateTime;
import java.time.format.DateTimeParseException;
import java.time.temporal.ChronoUnit;
import java.util.*;

public class PrivacyQueryFactory {
    private static final Preprocessor[] preprocessors = {
            StripOrderBy.INSTANCE,
            StripUnaryOpSubquery.INSTANCE,
            DesugarLeftJoinIntoInner.INSTANCE,
            DesugarLeftJoinIntoUnion.INSTANCE,
            StripSum.INSTANCE,
    };

    public static PrivacyQuery createPrivacyQuery(ParserResult result, SchemaPlusWithKey schema, Object[] parameters,
                                                  List<String> paramNames)
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
        ArrayList<Object> newParams = new ArrayList<>(Arrays.asList(parameters));
        ArrayList<String> newParamNames = new ArrayList<>(paramNames);
        result = ExtractParams.perform(result, newParams, newParamNames);

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
        }
        result.setParsedSql(sb.toString());

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
