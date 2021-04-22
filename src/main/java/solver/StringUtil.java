package solver;

public class StringUtil {
    public static String expandStringToInteger(String s) {
        StringBuilder out = new StringBuilder("1");
        for (int i = 0; i < s.length(); ++i) {
            out.append(String.format("%05d", (int) s.charAt(i)));
        }
        return out.toString();
    }
}
