package plugin.jdbc;

import org.apache.calcite.runtime.ResultSetEnumerable;
import org.apache.calcite.schema.Schema;

import org.apache.commons.lang.Validate;

import com.google.common.collect.ImmutableMap;

import sql.PrivacyException;

import plugin.Executor;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.PrintWriter;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.SQLFeatureNotSupportedException;
import java.sql.Statement;

import java.util.Iterator;
import java.util.Map;

import javax.sql.DataSource;
/**
 * Contains common functions for all Data sources that support JDBC.
 */
public abstract class JdbcDB implements Executor {
    private static final Logger LOG = LoggerFactory.getLogger(JdbcDB.class);

    public abstract Connection getConnection() throws ClassNotFoundException, SQLException;
    protected abstract String getCatalogSql();

    protected final String url;
    protected final String user;
    protected final String password;

    JdbcDB(Map<String, Object> properties) {
        validate(properties);
        this.url = (String) properties.get("url");
        this.user = (String) properties.get("username");
        this.password = (String) properties.get("password");
    }

    private void validate(Map<String, Object> properties) {
        Validate.notNull(properties.get("url"), "Field \"url\" specifying JDBC endpoint needs "
                + "to be defined for JDBC Data Source in JSON");
        Validate.notNull(properties.get("username"), "Field \"username\" specifying username needs "
                + "to be defined for JDBC Data Source in JSON");
        Validate.notNull(properties.get("password"), "Field \"password\" specifying password "
                + "to be defined for JDBC Data Source in JSON");
    }

    public ImmutableMap<String, Schema> getSchemas() throws PrivacyException {
        Connection conn = null;
        Statement stmt = null;
        try {
            conn = this.getConnection();
            stmt = conn.createStatement();
            ResultSet rs = stmt.executeQuery(this.getCatalogSql());
            //This is the problem!
            ImmutableMap<String, Schema> schemaMap = getSchemaFromResultSet(rs, this.getTypes(conn));

            rs.close();
            return schemaMap;
        } catch (ClassNotFoundException | SQLException s) {
            throw new PrivacyException(s);
        } finally {
            try {
                if (stmt != null) {
                    stmt.close();
                }

                if (conn != null) {
                    conn.close();
                }
            } catch (SQLException e) {
                LOG.error("Exception thrown while closing connection to "
                        + this.url + " " + e.getMessage(), e);
            }
        }
    }

    protected ImmutableMap<String, Integer> getTypes(Connection connection) throws SQLException {
        DatabaseMetaData databaseMetaData = connection.getMetaData();
        ResultSet rs = databaseMetaData.getTypeInfo();
        ImmutableMap.Builder<String, Integer> builder = new ImmutableMap.Builder<>();
        while (rs.next()) {
            LOG.debug("Registering data type '" + rs.getString("TYPE_NAME") + "'");
            builder.put(rs.getString("TYPE_NAME").toUpperCase(), rs.getInt("DATA_TYPE"));
        }

        return builder.build();
    }

    //Assuming rs.getString(1) => schemaname, rs.getString(2) => tableName,
    // rs.getString(3) => columnName, rs.getString(4) => columnType
    private ImmutableMap<String, Schema> getSchemaFromResultSet(ResultSet rs,
                                                                ImmutableMap<String, Integer>
                                                                        dataTypes)
            throws SQLException {
        if (rs == null || !rs.next()) {
            return ImmutableMap.of();
        }
        ImmutableMap.Builder<String, Schema> schemaBuilder = new ImmutableMap.Builder<>();

        while (!rs.isAfterLast()) {
            String currentSchema = rs.getString(1);
            String schemaKey = currentSchema;
            if (!this.isCaseSensitive()) {
                schemaKey = currentSchema.toUpperCase();
            }

            schemaBuilder.put(schemaKey, new JdbcSchema(currentSchema,
                    rs, this.isCaseSensitive(), dataTypes));
        }
        return schemaBuilder.build();
    }

    public Iterator<Object> executeQuery(final String sql)
            throws Exception {
        cleanup();
        return execute(this.getConnection(), sql);
    }

    public Iterator<Object> execute(final Connection conn, final String sql)
            throws Exception {
        return ResultSetEnumerable.of(
                new DataSource() {
                    @Override
                    public Connection getConnection() throws SQLException {
                        return conn;
                    }

                    @Override
                    public Connection getConnection(String s, String s1)
                            throws SQLException {
                        return conn;
                    }

                    @Override
                    public PrintWriter getLogWriter() throws SQLException {
                        return null;
                    }

                    @Override
                    public void setLogWriter(PrintWriter printWriter)
                            throws SQLException {

                    }

                    @Override
                    public void setLoginTimeout(int i) throws SQLException {

                    }

                    @Override
                    public int getLoginTimeout() throws SQLException {
                        return 100;
                    }

                    @Override
                    public java.util.logging.Logger getParentLogger()
                            throws SQLFeatureNotSupportedException {
                        return null;
                    }

                    @Override
                    public <T> T unwrap(Class<T> aClass) throws SQLException {
                        return null;
                    }

                    @Override
                    public boolean isWrapperFor(Class<?> aClass) throws SQLException {
                        return false;
                    }
                },
                sql
        ).iterator();
    }


    /**
     * Cleans up the JDBC resource without waiting for the Garbage Collection
     *
     * @throws SQLException
     */
    @Override
    public void cleanup() throws SQLException {
    }

    @Override
    public boolean isCaseSensitive() {
        return false;
    }
}
