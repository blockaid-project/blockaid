package sql;

import java.util.Collections;
import java.util.List;

public class PrivacyQueryFactory {

    public static PrivacyQuery createPrivacyQuery(ParserResult result)
    {
        return createPrivacyQuery(result, new Object[0], Collections.emptyList());
    }

    public static PrivacyQuery createPrivacyQuery(ParserResult result, Object[] parameters, List<String> paramNames)
    {
        if (result == null){
            return null;
        }
        switch(result.getKind()) {
            case SELECT:
                return new PrivacyQuerySelect(result, parameters, paramNames);
            default:
                throw new AssertionError("unexpected");
        }
    }
}
