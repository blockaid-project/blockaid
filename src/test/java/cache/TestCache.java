package cache;

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static junit.framework.TestCase.assertTrue;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;

public class TestCache {
    @Test
    public void testCachedQueryTrace() {
        CachedQueryTrace cacheTrace = new CachedQueryTrace();

        QueryTraceEntry q3 = new QueryTraceEntry(
                "SELECT * FROM people WHERE owner_id = ?_MY_UID",
                Collections.singletonList(null),
                Collections.singletonMap("_MY_UID", null)
        );
        q3.tuples.add(Arrays.asList(null, null, null, null));
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q3,
                Collections.singletonList(null),
                Collections.singletonList(Arrays.asList(new CachedQueryTraceEntry.Index(1), null, null, null))
        ));

        QueryTraceEntry q4 = new QueryTraceEntry(
                "SELECT * FROM posts WHERE id = ?? AND author_id = ??",
                Arrays.asList(null, null),
                Collections.emptyMap()
        );
        q4.tuples.add(Arrays.asList(null, null, null, null));
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q4,
                Arrays.asList(new CachedQueryTraceEntry.Index(2), new CachedQueryTraceEntry.Index(1)),
                Collections.singletonList(Arrays.asList(null, null, null, null)))
        );

        QueryTraceEntry q5 = new QueryTraceEntry(
                "SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??",
                Arrays.asList(null, null),
                Collections.emptyMap()
        );
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q5,
                Arrays.asList(new CachedQueryTraceEntry.Index(2), null),
                Collections.emptyList())
        );

        QueryTrace testTrace = new QueryTrace();

        testTrace.startQuery("SELECT * FROM users WHERE id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery("SELECT posts.* FROM posts INNER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE posts.id = ?? AND share_visibilities.user_id = ?_MY_UID", Arrays.asList(10, 1), Collections.singletonMap("_MY_UID", 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT * FROM people WHERE owner_id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery("SELECT * FROM posts WHERE id = ?? AND author_id = ??", Arrays.asList(10, 1), Collections.emptyMap());
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??", Arrays.asList(10, 3), Collections.emptyMap());

        assertTrue(cacheTrace.checkQueryTrace(testTrace));

        // parameter differs from row
        testTrace = new QueryTrace();

        testTrace.startQuery("SELECT * FROM users WHERE id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery("SELECT posts.* FROM posts INNER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE posts.id = ?? AND share_visibilities.user_id = ?_MY_UID", Arrays.asList(10, 1), Collections.singletonMap("_MY_UID", 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT * FROM people WHERE owner_id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery("SELECT * FROM posts WHERE id = ?? AND author_id = ??", Arrays.asList(10, 2), Collections.emptyMap());
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??", Arrays.asList(10, 3), Collections.emptyMap());

        assertFalse(cacheTrace.checkQueryTrace(testTrace));

        // empty set when nonempty expected
        testTrace = new QueryTrace();

        testTrace.startQuery("SELECT * FROM users WHERE id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery("SELECT posts.* FROM posts INNER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE posts.id = ?? AND share_visibilities.user_id = ?_MY_UID", Arrays.asList(10, 1), Collections.singletonMap("_MY_UID", 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT * FROM people WHERE owner_id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery("SELECT * FROM posts WHERE id = ?? AND author_id = ??", Arrays.asList(10, 1), Collections.emptyMap());
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??", Arrays.asList(10, 3), Collections.emptyMap());

        assertFalse(cacheTrace.checkQueryTrace(testTrace));

        // parameter differs only on most recent query
        testTrace = new QueryTrace();

        testTrace.startQuery("SELECT * FROM users WHERE id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery("SELECT posts.* FROM posts INNER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE posts.id = ?? AND share_visibilities.user_id = ?_MY_UID", Arrays.asList(10, 1), Collections.singletonMap("_MY_UID", 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT * FROM people WHERE owner_id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery("SELECT * FROM posts WHERE id = ?? AND author_id = ??", Arrays.asList(10, 1), Collections.emptyMap());
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??", Arrays.asList(11, 3), Collections.emptyMap());

        assertFalse(cacheTrace.checkQueryTrace(testTrace));

        // _MY_UID set differently by unused query
        testTrace = new QueryTrace();

        testTrace.startQuery("SELECT * FROM users WHERE id = ?_MY_UID", Collections.singletonList(44), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery("SELECT posts.* FROM posts INNER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE posts.id = ?? AND share_visibilities.user_id = ?_MY_UID", Arrays.asList(10, 1), Collections.singletonMap("_MY_UID", 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT * FROM people WHERE owner_id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery("SELECT * FROM posts WHERE id = ?? AND author_id = ??", Arrays.asList(10, 1), Collections.emptyMap());
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??", Arrays.asList(10, 3), Collections.emptyMap());

        assertFalse(cacheTrace.checkQueryTrace(testTrace));
    }

    @Test
    public void testCache() {
        CachedQueryTrace cacheTrace = new CachedQueryTrace();

        QueryTraceEntry q3 = new QueryTraceEntry(
                "SELECT * FROM people WHERE owner_id = ?_MY_UID",
                Collections.singletonList(null),
                Collections.singletonMap("_MY_UID", null)
        );
        q3.tuples.add(Arrays.asList(null, null, null, null));
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q3,
                Collections.singletonList(null),
                Collections.singletonList(Arrays.asList(new CachedQueryTraceEntry.Index(1), null, null, null))
        ));

        QueryTraceEntry q4 = new QueryTraceEntry(
                "SELECT * FROM posts WHERE id = ?? AND author_id = ??",
                Arrays.asList(null, null),
                Collections.emptyMap()
        );
        q4.tuples.add(Arrays.asList(null, null, null, null));
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q4,
                Arrays.asList(new CachedQueryTraceEntry.Index(2), new CachedQueryTraceEntry.Index(1)),
                Collections.singletonList(Arrays.asList(null, null, null, null)))
        );

        QueryTraceEntry q5 = new QueryTraceEntry(
                "SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??",
                Arrays.asList(null, null),
                Collections.emptyMap()
        );
        cacheTrace.addEntry(new CachedQueryTraceEntry(
                q5,
                Arrays.asList(new CachedQueryTraceEntry.Index(2), null),
                Collections.emptyList())
        );

        TraceCache cache = new TraceCache();
        cache.addToCache("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??", cacheTrace, true);

        QueryTrace testTrace = new QueryTrace();

        testTrace.startQuery("SELECT * FROM users WHERE id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery("SELECT posts.* FROM posts INNER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE posts.id = ?? AND share_visibilities.user_id = ?_MY_UID", Arrays.asList(10, 1), Collections.singletonMap("_MY_UID", 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT * FROM people WHERE owner_id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery("SELECT * FROM posts WHERE id = ?? AND author_id = ??", Arrays.asList(10, 1), Collections.emptyMap());
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??", Arrays.asList(10, 3), Collections.emptyMap());

        assertTrue(cache.checkCache(testTrace));

        // parameter differs from row
        testTrace = new QueryTrace();

        testTrace.startQuery("SELECT * FROM users WHERE id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery("SELECT posts.* FROM posts INNER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE posts.id = ?? AND share_visibilities.user_id = ?_MY_UID", Arrays.asList(10, 1), Collections.singletonMap("_MY_UID", 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT * FROM people WHERE owner_id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery("SELECT * FROM posts WHERE id = ?? AND author_id = ??", Arrays.asList(10, 2), Collections.emptyMap());
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??", Arrays.asList(10, 3), Collections.emptyMap());

        assertNull(cache.checkCache(testTrace));

        // empty set when nonempty expected
        testTrace = new QueryTrace();

        testTrace.startQuery("SELECT * FROM users WHERE id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery("SELECT posts.* FROM posts INNER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE posts.id = ?? AND share_visibilities.user_id = ?_MY_UID", Arrays.asList(10, 1), Collections.singletonMap("_MY_UID", 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT * FROM people WHERE owner_id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery("SELECT * FROM posts WHERE id = ?? AND author_id = ??", Arrays.asList(10, 1), Collections.emptyMap());
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??", Arrays.asList(10, 3), Collections.emptyMap());

        assertNull(cache.checkCache(testTrace));

        // parameter differs only on most recent query
        testTrace = new QueryTrace();

        testTrace.startQuery("SELECT * FROM users WHERE id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery("SELECT posts.* FROM posts INNER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE posts.id = ?? AND share_visibilities.user_id = ?_MY_UID", Arrays.asList(10, 1), Collections.singletonMap("_MY_UID", 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT * FROM people WHERE owner_id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery("SELECT * FROM posts WHERE id = ?? AND author_id = ??", Arrays.asList(10, 1), Collections.emptyMap());
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??", Arrays.asList(11, 3), Collections.emptyMap());

        assertNull(cache.checkCache(testTrace));

        // _MY_UID set differently by unused query
        testTrace = new QueryTrace();

        testTrace.startQuery("SELECT * FROM users WHERE id = ?_MY_UID", Collections.singletonList(44), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "john_doe", "john_doe@example.com")));

        testTrace.startQuery("SELECT posts.* FROM posts INNER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE posts.id = ?? AND share_visibilities.user_id = ?_MY_UID", Arrays.asList(10, 1), Collections.singletonMap("_MY_UID", 1));
        testTrace.endQuery(Collections.emptyList());

        testTrace.startQuery("SELECT * FROM people WHERE owner_id = ?_MY_UID", Collections.singletonList(1), Collections.singletonMap("_MY_UID", 0));
        testTrace.endQuery(Collections.singletonList(Arrays.asList(1, "78ff4567-89ab-cdef-0123-456789abcdef", 1, "john_doe@example.com")));

        testTrace.startQuery("SELECT * FROM posts WHERE id = ?? AND author_id = ??", Arrays.asList(10, 1), Collections.emptyMap());
        testTrace.endQuery(Collections.singletonList(Arrays.asList(10, 1, false, "10cd4567-89ab-cdef-0123-456789abcdef")));

        testTrace.startQuery("SELECT id FROM mentions WHERE mentions_container_id = ?? AND mentions_container_type = 'Post' AND person_id = ??", Arrays.asList(10, 3), Collections.emptyMap());

        assertNull(cache.checkCache(testTrace));
    }
}
