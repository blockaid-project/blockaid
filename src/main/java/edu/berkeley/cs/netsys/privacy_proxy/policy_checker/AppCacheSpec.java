package edu.berkeley.cs.netsys.privacy_proxy.policy_checker;

import com.google.common.collect.ImmutableList;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class AppCacheSpec {
    private static final Pattern PARAM_PATTERN = Pattern.compile("\\?([A-Za-z_]+)");

    // For example, `raw_score/submissions/(?<submissionId>\d+)-\d+/assessments/(?<assessmentId>\d+)-\d+`.
    private final Pattern keyPattern;
    // For each template, the query is parameterized and the params contain the group name for each param.
    private final ImmutableList<QueryWithParams<String>> queryTemplates;

    public static AppCacheSpec fromSpecString(String spec) {
        List<String> parts = Arrays.stream(spec.split("!")).map(String::strip).collect(Collectors.toList());
        String keyPatternStr = parts.get(0);
        parts.remove(0);

        ImmutableList.Builder<QueryWithParams<String>> qts = new ImmutableList.Builder<>();
        for (String qt : parts) {
            ImmutableList.Builder<String> groupNames = new ImmutableList.Builder<>();
            StringBuilder sb = new StringBuilder();
            Matcher pm = PARAM_PATTERN.matcher(qt);
            while (pm.find()) {
                groupNames.add(pm.group(1));
                pm.appendReplacement(sb, "?");
            }
            pm.appendTail(sb);
            qts.add(new QueryWithParams<>(sb.toString(), groupNames.build()));
        }

        return new AppCacheSpec(keyPatternStr, qts.build());
    }

    private AppCacheSpec(String keyPatternStr, Collection<QueryWithParams<String>> queryTemplates) {
        this.keyPattern = Pattern.compile(keyPatternStr);
        this.queryTemplates = ImmutableList.copyOf(queryTemplates);
    }

    public Optional<List<QueryWithParams<Object>>> getQueries(String key) {
        Matcher km = keyPattern.matcher(key);
        if (!km.matches()) {
            return Optional.empty();
        }

        ArrayList<QueryWithParams<Object>> res = new ArrayList<>();
        for (QueryWithParams<String> qt : queryTemplates) {
            ImmutableList<Object> params = qt.params().stream().map(km::group)
                    .map(Integer::parseInt) // TODO(zhangwen): currently only supports integers.
                    .collect(ImmutableList.toImmutableList());
            res.add(new QueryWithParams<>(qt.query(), params));
        }

        return Optional.of(res);
    }

    public record QueryWithParams<T>(String query, ImmutableList<T> params) {}
}
