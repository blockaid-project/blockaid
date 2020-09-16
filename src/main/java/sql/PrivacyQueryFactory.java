package sql;

public class PrivacyQueryFactory {

    public static PrivacyQuery createPrivacyQuery(ParserResult result)
    {
        if (result == null){
            return null;
        }
        System.out.println("result type is " + result.getKind());
        switch(result.getKind()) {
            case SELECT:
                return new PrivacyQuerySelect(result);
                 default:
                throw new AssertionError("unexpected");
        }
    }
}
