package edu.berkeley.cs.netsys.privacy_proxy.cache;

import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTrace;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import com.google.common.collect.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Tuple;
import edu.berkeley.cs.netsys.privacy_proxy.sql.ParserResult;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.*;

public class DecisionTemplate {
    private final ImmutableList<Entry> entries;
    private final ImmutableMap<String, Integer> constName2EC;
    private final ImmutableMap<String, Object> constName2Value; // Only supports non-null values.

    private final ImmutableList<LessThan> lts;
    private final ImmutableMultimap<Integer, LessThan> ec2LessThan; // Maps EC to relevant less-than constraints.

    public DecisionTemplate(List<Entry> entries, Map<String, Integer> constName2EC,
                            Map<String, Object> constName2Value, Collection<LessThan> lts) {
        // Assert that constName2EC and constName2Value don't intersect.
        for (String constName : constName2EC.keySet()) {
            checkArgument(!constName2Value.containsKey(constName),
                    "constant " + constName + " appears has both EC and value");
        }

        long numCurrent = entries.stream().filter(e -> e.isCurrentQuery).count();
        checkArgument(numCurrent == 1, "must be exactly one current query, got " + numCurrent);

        this.entries = ImmutableList.copyOf(entries);
        this.constName2EC = ImmutableMap.copyOf(constName2EC);
        this.constName2Value = ImmutableMap.copyOf(constName2Value);

        this.lts = ImmutableList.copyOf(lts);
        ImmutableMultimap.Builder<Integer, LessThan> builder = new ImmutableMultimap.Builder<>();
        for (LessThan lt : lts) {
            builder.put(lt.lhsEC(), lt);
            builder.put(lt.rhsEC(), lt);
        }
        this.ec2LessThan = builder.build();
    }

    public boolean doesMatch(QueryTrace trace) {
        PushPopMap<Integer, Object> ec2Value = new PushPopMap<>(this::checkLessThan);
        if (!matchConstants(trace, ec2Value)) {
            return false;
        }

        return matchQueries(trace, ec2Value, entries.listIterator());
    }

    private boolean checkLessThan(Map<Integer, Object> ec2Value, int ecIdx) {
        for (LessThan lt : ec2LessThan.get(ecIdx)) {
            if (!ec2Value.containsKey(lt.lhsEC()) || !ec2Value.containsKey(lt.rhsEC())) {
                continue;
            }
            Object lhsValue = ec2Value.get(lt.lhsEC()), rhsValue = ec2Value.get(lt.rhsEC());
            if (!Tuple.valueLessThan(lhsValue, rhsValue)) {
                return false;
            }
        }
        return true;
    }

    private boolean matchConstants(QueryTrace trace, PushPopMap<Integer, Object> ec2Value) {
        Map<String, Object> constMap = trace.getConstMap();
        for (Map.Entry<String, Object> e : constName2Value.entrySet()) {
            checkArgument(constMap.containsKey(e.getKey()));
            if (!constMap.get(e.getKey()).equals(e.getValue())) {
                return false;
            }
        }

        for (Map.Entry<String, Integer> e : constName2EC.entrySet()) {
            String constName = e.getKey();
            checkArgument(constMap.containsKey(constName));

            int ecIdx = e.getValue();
            Object constValue = constMap.get(constName);

            if (!ec2Value.ensureMapping(ecIdx, constValue)) {
                return false;
            }
        }
        return true;
    }

    private boolean matchQueries(QueryTrace trace, PushPopMap<Integer, Object> ec2Value, ListIterator<Entry> it) {
        if (!it.hasNext()) {
            return true;
        }

        Entry thisEntry = it.next();
        try {
            if (thisEntry.isCurrentQuery) {
                QueryTraceEntry qte = trace.getCurrentQuery();
                if (!qte.getParserResult().equals(thisEntry.qpr)) {
                    return false;
                }
                ec2Value.push();
                try {
                    if (!thisEntry.matchParams(qte, ec2Value)) {
                        return false;
                    }
                    return matchQueries(trace, ec2Value, it);
                } finally {
                    ec2Value.pop();
                }
            }

            for (QueryTraceEntry qte : trace.getEntriesByQuery(thisEntry.qpr)) {
                ec2Value.push();
                try {
                    if (!thisEntry.matchParams(qte, ec2Value)) {
                        continue;
                    }

                    for (List<Object> tup : qte.getTuples()) {
                        ec2Value.push();
                        if (thisEntry.matchTuple(tup, ec2Value) && matchQueries(trace, ec2Value, it)) {
                            return true;
                        }
                        ec2Value.pop();
                    }
                } finally {
                    ec2Value.pop();
                }
            }
        } finally {
            it.previous();
        }

        return false;
    }

    @Override
    public String toString() {
        ArrayList<String> lines = new ArrayList<>();

        for (Map.Entry<String, Integer> e : constName2EC.entrySet()) {
            lines.add(String.format("%s = ?%d", e.getKey(), e.getValue()));
        }
        for (Map.Entry<String, Object> e : constName2Value.entrySet()) {
            lines.add(String.format("%s = %s", e.getKey(), e.getValue()));
        }

        String currQueryText = null;
        Multimap<String, Entry> entriesByStr = ArrayListMultimap.create();
        for (Entry entry : entries) {
            if (entry.isCurrentQuery) {
                currQueryText = entry.toStringQuery();
            } else {
                entriesByStr.put(entry.toStringQuery(), entry);
            }
        }
        checkState(currQueryText != null);

        for (String queryText : entriesByStr.keySet()) {
            lines.add(queryText);
            for (Entry entry : entriesByStr.get(queryText)) {
                lines.add("    " + entry.toStringRow());
            }
        }

        for (LessThan lt : lts) {
            lines.add(String.format("?%d < ?%d", lt.lhsEC(), lt.rhsEC()));
        }

        lines.add("--------------------------------------------------------------------------------");
        lines.add(currQueryText);

        return String.join("\n", lines);
    }

    // A less-than constraint between equivalence classes.  Value operands not yet supported.
    public record LessThan(int lhsEC, int rhsEC) {}

    // The existence of a (previous query, returned row)-pair, or constraints on the current query.
    public static class Entry {
        private final ParserResult qpr;
        private String convertedQueryText = null; // With query parameters substituted with ECs / values; lazily computed.
        private final boolean isCurrentQuery;

        // Maps query parameter index -> what value it must take.
        private final ImmutableMap<Integer, Object> paramIdx2Value; // Only supports non-null values.
        // Maps query parameter index -> which equivalence class it belongs to.
        private final ImmutableMap<Integer, Integer> paramIdx2EC;

        // The following two structures exist only for queries that are not the current.
        // Maps row attribute index -> what value it must take.
        private final Map<Integer, Object> rowAttrIdx2Value; // Can have nulls.
        // Maps row attribute index -> which equivalence class it belongs to.
        private final ImmutableMap<Integer, Integer> rowAttrIdx2EC;

        private Entry(ParserResult query, boolean isCurrentQuery, ImmutableMap<Integer, Object> paramIdx2Value,
                     ImmutableMap<Integer, Integer> paramIdx2EC, Map<Integer, Object> rowAttrIdx2Value,
                     ImmutableMap<Integer, Integer> rowAttrIdx2EC) {
            this.qpr = query;
            this.isCurrentQuery = isCurrentQuery;

            if (isCurrentQuery) {
                checkArgument(rowAttrIdx2EC.isEmpty());
                checkArgument(rowAttrIdx2Value.isEmpty());
            }

            this.paramIdx2Value = paramIdx2Value;
            this.paramIdx2EC = paramIdx2EC;
            this.rowAttrIdx2Value = rowAttrIdx2Value;
            this.rowAttrIdx2EC = rowAttrIdx2EC;
        }

        public String toStringQuery() {
            if (convertedQueryText == null) {
                StringBuilder sb = new StringBuilder();
                Pattern pattern = Pattern.compile("\\?");
                Matcher matcher = pattern.matcher(qpr.getParsedSql());
                int i = 0;
                while (matcher.find()) {
                    matcher.appendReplacement(sb, "");
                    Integer ecIdx = paramIdx2EC.get(i);
                    Object value = paramIdx2Value.get(i);
                    if (ecIdx != null) {
                        sb.append("?").append(ecIdx);
                    } else if (value != null) {
                        if (value instanceof String) {
                            sb.append("\"").append(value).append("\"");
                        } else {
                            sb.append(value);
                        }
                    } else {
                        sb.append("*");
                    }
                    ++i;
                }
                matcher.appendTail(sb);
                convertedQueryText = sb.toString();
            }
            return convertedQueryText;
        }

        public String toStringRow() {
            checkState(!isCurrentQuery);

            String body = Stream.concat( // These two maps should have no overlapping keys.
                    rowAttrIdx2Value.keySet().stream(),
                    rowAttrIdx2EC.keySet().stream()
            ).sorted().map(i -> {
                String rhs;
                Integer ecIdx = rowAttrIdx2EC.get(i);
                if (ecIdx != null) {
                    rhs = "?" + ecIdx;
                } else {
                    rhs = Objects.toString(rowAttrIdx2Value.get(i));
                }
                return String.format(".%d = %s", i, rhs);
            }).collect(Collectors.joining(", "));

            return "{" + body + "}";
        }

        @Override
        public String toString() {
            if (isCurrentQuery) {
                return toStringQuery();
            }
            return toStringQuery() + "\n\t" + toStringRow();
        }

        private boolean matchParams(QueryTraceEntry qte, PushPopMap<Integer, Object> ec2Value) {
            return matchHelper(qte.getParameters(), paramIdx2Value, paramIdx2EC, ec2Value);
        }

        private boolean matchTuple(List<Object> tup, PushPopMap<Integer, Object> ec2Value) {
            return matchHelper(tup, rowAttrIdx2Value, rowAttrIdx2EC, ec2Value);
        }

        private static boolean matchHelper(List<Object> target, Map<Integer, Object> idx2Value,
                                    Map<Integer, Integer> idx2EC, PushPopMap<Integer, Object> ec2Value) {
            for (Map.Entry<Integer, Object> e : idx2Value.entrySet()) {
                if (!Objects.equals(e.getValue(), target.get(e.getKey()))) {
                    return false;
                }
            }
            for (Map.Entry<Integer, Integer> e : idx2EC.entrySet()) {
                int idx = e.getKey(), ecIdx = e.getValue();
                if (!ec2Value.ensureMapping(ecIdx, target.get(idx))) {
                    return false;
                }
            }
            return true;
        }
    }

    public static class EntryBuilder {
        private final QueryTraceEntry queryTraceEntry;
        private final boolean isCurrentQuery;

        private final Map<Integer, Object> paramIdx2Value;
        private final Map<Integer, Integer> paramIdx2EC;

        private final Map<Integer, Object> rowAttrIdx2Value;
        private final Map<Integer, Integer> rowAttrIdx2EC;

        public EntryBuilder(QueryTraceEntry queryTraceEntry, boolean isCurrentQuery) {
            this.queryTraceEntry = queryTraceEntry;
            this.isCurrentQuery = isCurrentQuery;

            this.paramIdx2Value = new HashMap<>();
            this.paramIdx2EC = new HashMap<>();
            this.rowAttrIdx2EC = new HashMap<>();
            this.rowAttrIdx2Value = new HashMap<>();
        }

        private void checkParamNotSet(int paramIdx) {
            checkArgument(!paramIdx2Value.containsKey(paramIdx), "param already has an assigned value");
            checkArgument(!paramIdx2EC.containsKey(paramIdx), "param already belongs to an EC");
        }

        private void checkRowAttrNotSet(int attrIdx) {
            checkState(!isCurrentQuery, "cannot set returned row attribute for the current query");
            checkArgument(!rowAttrIdx2Value.containsKey(attrIdx), "attribute already has an assigned value");
            checkArgument(!rowAttrIdx2EC.containsKey(attrIdx), "attribute already belongs to an EC");
        }

        public void setParamValue(int paramIdx, Object value) {
            checkNotNull(value);
            checkParamNotSet(paramIdx);
            paramIdx2Value.put(paramIdx, value);
        }

        public void setParamEC(int paramIdx, int ecIdx) {
            checkParamNotSet(paramIdx);
            paramIdx2EC.put(paramIdx, ecIdx);
        }

        public void setRowAttrValue(int attrIdx, Object value) {
            checkRowAttrNotSet(attrIdx);
            rowAttrIdx2Value.put(attrIdx, value);
        }

        public void setRowAttrEC(int attrIdx, int ecIdx) {
            checkRowAttrNotSet(attrIdx);
            rowAttrIdx2EC.put(attrIdx, ecIdx);
        }

        public Entry build() {
            return new Entry(
                    queryTraceEntry.getParserResult(),
                    isCurrentQuery,
                    ImmutableMap.copyOf(paramIdx2Value),
                    ImmutableMap.copyOf(paramIdx2EC),
                    // TODO(zhangwen): make this map immutable.
                    rowAttrIdx2Value, // Use regular map because immutable maps don't allow null values.
                    ImmutableMap.copyOf(rowAttrIdx2EC)
            );
        }
    }
}
