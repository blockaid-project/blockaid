package cache.trace;

import java.util.List;
import java.util.Map;

public interface UnmodifiableLinearQueryTrace {
    Map<String, Integer> getConstMap();
    List<QueryTraceEntry> getAllEntries();
    QueryTraceEntry getCurrentQuery();
}
