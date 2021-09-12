package policy_checker;

import com.google.common.collect.ImmutableList;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class AppCacheSpec {
    private static final Pattern PARAM_PATTERN = Pattern.compile("\\?([A-Za-z_]+)");

    private final Pattern keyPattern;
    private final ImmutableList<String> queryTemplates;

    public static AppCacheSpec fromSpecString(String spec) {
        List<String> parts = Arrays.stream(spec.split("!")).map(String::strip).collect(Collectors.toList());
        String keyPatternStr = parts.get(0);
        parts.remove(0);
        return new AppCacheSpec(keyPatternStr, parts);
    }

    public AppCacheSpec(String keyPatternStr, Collection<String> queryTemplates) {
        this.keyPattern = Pattern.compile(keyPatternStr);
        this.queryTemplates = ImmutableList.copyOf(queryTemplates);
    }

    public Optional<List<String>> getQueries(String key) {
        Matcher km = keyPattern.matcher(key);
        if (!km.matches()) {
            return Optional.empty();
        }

        ArrayList<String> res = new ArrayList<>();
        for (String qt : queryTemplates) {
            StringBuilder sb = new StringBuilder();
            Matcher pm = PARAM_PATTERN.matcher(qt);
            while (pm.find()) {
                String value = km.group(pm.group(1));
                pm.appendReplacement(sb, value);
            }
            pm.appendTail(sb);
            res.add(sb.toString());
        }

        return Optional.of(res);
    }
}
