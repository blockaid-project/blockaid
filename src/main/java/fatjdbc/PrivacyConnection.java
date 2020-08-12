package fatjdbc;

import org.apache.calcite.adapter.java.JavaTypeFactory;
import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.schema.SchemaPlus;
import sql.PrivacyException;

import java.sql.Connection;
import java.sql.SQLException;
import java.util.Properties;

/**
 * Privacy-specific {@link Connection}.
 *
 * @see #unwrap
 */
public interface PrivacyConnection extends Connection {
    /**
     * Returns the root schema.
     * <p>You can define objects (such as relations) in this schema, and
     * also nested schemas.</p>
     *
     * @return Root schema
     */
    SchemaPlus getRootSchema() throws PrivacyException;

    /**
     * Returns the type factory.
     *
     * @return Type factory
     */
    JavaTypeFactory getTypeFactory();

    /**
     * Returns an instance of the connection properties.
     * <p>
     * NOTE: The resulting collection of properties is same collection used
     * by the connection, and is writable, but behavior if you modify the
     * collection is undefined. Some implementations might, for example, see
     * a modified property, but only if you set it before you create a
     * statement. We will remove this method when there are better
     * implementations of stateful connections and configuration.
     * </p>
     *
     * @return properties
     */
    Properties getProperties();

    // in java.sql.Connection from JDK 1.7, but declare here to allow other JDKs
    void setSchema(String schema) throws SQLException;

    // in java.sql.Connection from JDK 1.7, but declare here to allow other JDKs
    String getSchema() throws SQLException;

    CalciteConnectionConfig config();
}
