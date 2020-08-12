package plugin.jdbc;

import org.apache.calcite.sql.SqlDialect;

import com.google.common.collect.ImmutableMap;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.Map;
import java.util.Properties;


public class H2Db extends JdbcDB {
    private final String catalogSql = "SELECT TABLE_SCHEMA, TABLE_NAME, COLUMN_NAME, TYPE_NAME "
            + "FROM INFORMATION_SCHEMA.COLUMNS WHERE TABLE_SCHEMA != 'INFORMATION_SCHEMA' "
            + "ORDER BY TABLE_SCHEMA, TABLE_NAME, ORDINAL_POSITION";

    private final String defaultSchema = "PUBLIC";
    private final String productName = "H2";

    private static final ImmutableMap<String, String> DATA_TYPES =
            new ImmutableMap.Builder<String, String>()
                    .put("integer", "integer")
                    .put("character varying", "character varying")
                    .put("-6", "smallint")
                    .put("-5", "integer")
                    .put("3", "double")
                    .put("4", "integer")
                    .put("5", "smallint")
                    .put("8", "double")
                    .put("12", "character varying")
                    .put("93", "timestamp")
                    .put("16", "boolean")
                    .put("1", "character")
                    .put("91", "date").build();

    public H2Db(Map<String, Object> properties) {
        super(properties);
    }

    public Connection getConnection() throws ClassNotFoundException, SQLException {
        Class.forName("org.h2.Driver");
        Properties props = new Properties();
        props.setProperty("user", user);
        props.setProperty("password", password);
        return DriverManager.getConnection(url, props);
    }

    @Override
    public String getCatalogSql() {
        return catalogSql;
    }

    @Override
    public String getDefaultSchema() {
        return defaultSchema;
    }

    @Override
    public String getProductName() {
        return productName;
    }

    @Override
    public SqlDialect getSqlDialect() {
        final SqlDialect h2Dialect =
                SqlDialect.getProduct("H2", null).getDialect();
        return h2Dialect;
    }
}