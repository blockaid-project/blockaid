package cache;

import org.junit.Test;
import solver.Query;
import solver.Schema;
import sql.ParserResult;
import sql.PrivacyQuery;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static junit.framework.TestCase.assertTrue;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;

public class TestCache {
    private static class FakeParserResult extends ParserResult {
        private FakeParserResult(String sql) {
            super(sql, null, null, false, false);
        }
    }

    private static class FakePrivacyQuery extends PrivacyQuery {
        private FakePrivacyQuery(String sql) {
            super(new FakeParserResult(sql));
        }

        @Override
        public List<String> getProjectColumns() {
            return null;
        }

        @Override
        public List<String> getThetaColumns() {
            return null;
        }

        @Override
        public List<String> getRelations() {
            return null;
        }

        @Override
        public Query getSolverQuery(Schema schema) {
            return null;
        }

        @Override
        public Query getSolverQuery(Schema schema, String paramPrefix, int offset) {
            return null;
        }

        @Override
        public List<Boolean> getResultBitmap() {
            return null;
        }
    }

    private static PrivacyQuery Q1 = new FakePrivacyQuery("SELECT * FROM users WHERE id = ?_MY_UID");
    private static PrivacyQuery Q2 = new FakePrivacyQuery("SELECT posts.* FROM posts INNER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE posts.id = ?? AND share_visibilities.user_id = ?_MY_UID");
    private static PrivacyQuery Q3 = new FakePrivacyQuery("SELECT * FROM people WHERE owner_id = ?_MY_UID");
    private static PrivacyQuery Q4 = new FakePrivacyQuery("SELECT * FROM posts WHERE id = ?? AND author_id = ??");
    private static PrivacyQuery Q5 = new FakePrivacyQuery("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??");

    @Test
    public void testCachedQueryTrace() {
        CachedQueryTrace cacheTrace = new CachedQueryTrace();

        QueryTraceEntry q3 = new QueryTraceEntry(
                Q3,
                Collections.singletonList(null)
        );
        q3.setTuples(List.of(Arrays.asList(null, null, null, null)));
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q3,
                false,
                Collections.singletonList(null),
                Collections.singletonList(Arrays.asList(new CachedQueryTraceEntry.Index(1), null, null, null))
        ));

        QueryTraceEntry q4 = new QueryTraceEntry(
                Q4,
                Arrays.asList(null, null)
        );
        q4.setTuples(List.of(Arrays.asList(null, null, null, null)));
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q4,
                false,
                Arrays.asList(new CachedQueryTraceEntry.Index(2), new CachedQueryTraceEntry.Index(1)),
                Collections.singletonList(Arrays.asList(null, null, null, null)))
        );

        QueryTraceEntry q5 = new QueryTraceEntry(
                Q5,
                Arrays.asList(null, null)
        );
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q5,
                true,
                Arrays.asList(new CachedQueryTraceEntry.Index(2), null),
                Collections.emptyList())
        );

        QueryTrace testTrace = new QueryTrace();

        testTrace.startQuery(Q1, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery(Q2, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery(Q3, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery(Q4, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery(Q5, Arrays.asList(10, 3));

        assertTrue(cacheTrace.checkQueryTrace(testTrace));

        // parameter differs from row
        testTrace = new QueryTrace();

        testTrace.startQuery(Q1, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery(Q2, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery(Q3, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery(Q4, Arrays.asList(10, 2));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery(Q5, Arrays.asList(10, 3));

        assertFalse(cacheTrace.checkQueryTrace(testTrace));

        // empty set when nonempty expected
        testTrace = new QueryTrace();

        testTrace.startQuery(Q1, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery(Q2, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery(Q3, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery(Q4, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery(Q5, Arrays.asList(10, 3));

        assertFalse(cacheTrace.checkQueryTrace(testTrace));

        // parameter differs only on most recent query
        testTrace = new QueryTrace();

        testTrace.startQuery(Q1, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery(Q2, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery(Q3, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery(Q4, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery(Q5, Arrays.asList(11, 3));

        assertFalse(cacheTrace.checkQueryTrace(testTrace));
    }

    @Test
    public void testCache() {
        CachedQueryTrace cacheTrace = new CachedQueryTrace();

        QueryTraceEntry q3 = new QueryTraceEntry(
                Q3,
                Collections.singletonList(null)
        );
        q3.setTuples(List.of(Arrays.asList(null, null, null, null)));
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q3,
                false,
                Collections.singletonList(null),
                Collections.singletonList(Arrays.asList(new CachedQueryTraceEntry.Index(1), null, null, null))
        ));

        QueryTraceEntry q4 = new QueryTraceEntry(
                Q4,
                Arrays.asList(null, null)
        );
        q4.setTuples(List.of(Arrays.asList(null, null, null, null)));
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q4,
                false,
                Arrays.asList(new CachedQueryTraceEntry.Index(2), new CachedQueryTraceEntry.Index(1)),
                Collections.singletonList(Arrays.asList(null, null, null, null)))
        );

        QueryTraceEntry q5 = new QueryTraceEntry(
                Q5,
                Arrays.asList(null, null)
        );
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q5,
                true,
                Arrays.asList(new CachedQueryTraceEntry.Index(2), null),
                Collections.emptyList())
        );

        TraceCache cache = new TraceCache();
        cache.addToCache(Q5.parsedSql.getParsedSql(), cacheTrace, true);

        QueryTrace testTrace = new QueryTrace();

        testTrace.startQuery(Q1, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery(Q2, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery(Q3, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery(Q4, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery(Q5, Arrays.asList(10, 3));

        assertTrue(cache.checkCache(testTrace));

        // parameter differs from row
        testTrace = new QueryTrace();

        testTrace.startQuery(Q1, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery(Q2, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery(Q3, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery(Q4, Arrays.asList(10, 2));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery(Q5, Arrays.asList(10, 3));

        assertNull(cache.checkCache(testTrace));

        // empty set when nonempty expected
        testTrace = new QueryTrace();

        testTrace.startQuery(Q1, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery(Q2, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery(Q3, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery(Q4, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery(Q5, Arrays.asList(10, 3));

        assertNull(cache.checkCache(testTrace));

        // parameter differs only on most recent query
        testTrace = new QueryTrace();

        testTrace.startQuery(Q1, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery(Q2, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery(Q3, Collections.singletonList(1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery(Q4, Arrays.asList(10, 1));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery(Q5, Arrays.asList(11, 3));

        assertNull(cache.checkCache(testTrace));
    }
}
