package plugin;

import java.util.Iterator;

/**
 * Adds capability to executeQuery a sql on a {@link DataSource}
 */
public interface Executor extends DataSource {

    Iterator<Object> executeQuery(String sql) throws Exception;

    void cleanup() throws Exception;
}