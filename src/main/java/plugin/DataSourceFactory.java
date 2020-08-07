package plugin;

import sql.PrivacyException;

import java.util.Map;

/**
 * Create a {@link DataSource} based on input. The factory can return different types of data
 * sources depending on the properties.
 */
public interface DataSourceFactory {
    DataSource create(Map<String, Object> properties) throws PrivacyException;
}
