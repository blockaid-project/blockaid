package plugin;

import org.apache.calcite.schema.Schema;
import org.apache.calcite.sql.SqlDialect;

import com.google.common.collect.ImmutableMap;

import sql.PrivacyException;


/**
 * A representation of a instance of a database or a data store. No assumptions are made on the
 * underlying technology. The only constraint is that the structure of the data can be
 * represented by schemas, tables and columns with a well-known data type.
 */
public interface DataSource {
    ImmutableMap<String, Schema> getSchemas() throws PrivacyException;
    String getDefaultSchema();
    String getProductName();
    SqlDialect getSqlDialect();
    boolean isCaseSensitive();
}
