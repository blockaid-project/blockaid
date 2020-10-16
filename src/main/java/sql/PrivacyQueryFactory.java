package sql;

public class PrivacyQueryFactory {

    public static PrivacyQuery createPrivacyQuery(ParserResult result)
    {
        return createPrivacyQuery(result, new Object[0]);
    }

    public static PrivacyQuery createPrivacyQuery(ParserResult result, Object[] parameters)
    {
        if (result == null){
            return null;
        }
        switch(result.getKind()) {
            case SELECT:
                return new PrivacyQuerySelect(result, parameters);
            default:
                throw new AssertionError("unexpected");
        }
    }
}
