package plugin.jdbc;

import org.apache.calcite.sql.SqlDialect;

import com.google.common.collect.ImmutableMap;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Map;

/**
 * Created by dev on 11/23/15.
 */
public class MysqlDB extends JdbcDB {
    private final String catalogSql = "select table_schema, "
            + "table_name, column_name, data_type from "
            + "information_schema.columns order by "
            + "table_schema, table_name, ordinal_position;";

    public static final ImmutableMap<String, String> DATATYPES =
            new ImmutableMap.Builder<String, String>()
                    .put("int\\([0-9]+\\)", "int")
                    .put("tinyint\\([0-9]+\\)", "int")
                    .put("smallint\\([0-9]+\\)", "smallint")
                    .put("mediumint\\([0-9]+\\)", "int")
                    .put("bigint\\([0-9]+\\)", "bigint")
                    .put("bigint\\([0-9]+\\)" + "( unsigned)*", "bigint")
                    .put("float\\([0-9]+,[0-9]+\\)?", "float")
                    .put("double\\([0-9]+,[0-9]+\\)?", "double")
                    .put("decimal\\([0-9]+,[0-9]+\\)", "double")
                    .put("datetime", "timestamp")
                    .put("char\\([0-9]+\\)", "char")
                    .put("varchar\\([0-9]+\\)", "character varying")
                    .put("text", "string")
                    .put("tinytext", "string")
                    .put("mediumtext", "string")
                    .put("longtext", "string").build();

    private String defaultSchema = null;
    private final String productName = "MYSQL";

    public MysqlDB(Map<String, Object> properties) {
        super(properties);
    }

    @Override
    public Connection getConnection() throws ClassNotFoundException, SQLException {
        Class.forName("com.mysql.jdbc.Driver");
        return DriverManager.getConnection(url, user, password);
    }

    @Override
    protected String getCatalogSql() {
        return catalogSql;
    }

    @Override
    public String getDefaultSchema() {
        if (defaultSchema == null) {
            try {
                ResultSet rs = this.getConnection().createStatement().executeQuery("SELECT DATABASE()");
                rs.next();
                defaultSchema = rs.getString(1);
            } catch (SQLException | ClassNotFoundException e) {
                throw new RuntimeException("Couldnot fetch DefaultSchema "
                        + "for mysql" + "Error:" + e.getMessage(), e);
            }
        }
        return defaultSchema;
    }

    @Override
    public String getProductName() {
        return productName;
    }

    @Override
    public SqlDialect getSqlDialect() {
        final SqlDialect sqlDialect = SqlDialect.getProduct("MySQL", null).getDialect();
        return sqlDialect;
    }

    @Override
    public boolean isCaseSensitive() {
        return true;
    }
}
