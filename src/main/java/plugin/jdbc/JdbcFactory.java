package plugin.jdbc;

import org.apache.commons.lang.Validate;

import com.google.common.collect.ImmutableMap;

import sql.PrivacyException;
import plugin.DataSource;
import plugin.DataSourceFactory;


import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.Map;

/**
 * Created by rajatv on 11/12/15.
 */
public class JdbcFactory implements DataSourceFactory {
    // Static Registry for JDBC DB plugin
    private static final Map<String, Class<? extends JdbcDB>> DB_PLUGINS =
            new ImmutableMap.Builder<String, Class<? extends JdbcDB>>()
                    .put("HIVE", EMRDb.class)
                    .put("REDSHIFT", RedShiftDb.class)
                    .put("H2", H2Db.class)
                    .put("MYSQL", MysqlDB.class)
                    .put("ORACLE", OracleDb.class)
                    .put("GENERIC", GenericDb.class)
                    .build();

    public DataSource create(Map<String, Object> properties) throws PrivacyException {
        validate(properties);
        String type = (String) properties.get("type");
        Class dbClass = DB_PLUGINS.get(type.toUpperCase());
        Validate.notNull(dbClass, "Invalid DataSource type: " + type
                + " Please specify one of these: "
                + Arrays.toString(DB_PLUGINS.keySet().toArray()));
        return getDataSource(properties, dbClass);
    }

    private DataSource getDataSource(Map<String, Object> properties,
                                     Class dbClass) throws PrivacyException {
        try {
            return (DataSource) (dbClass.getConstructor(Map.class)
                    .newInstance(properties));
        } catch (NoSuchMethodException | IllegalAccessException | InstantiationException e) {
            throw new PrivacyException(new Throwable("Invoking invalid constructor on class "
                    + "specified for type " + properties.get("type") + ": " + dbClass.getCanonicalName()));
        } catch (InvocationTargetException e) {
            throw new PrivacyException(e.getTargetException());
        }
    }

    private void validate(Map<String, Object> properties) {
        Validate.notNull(properties.get("type"),
                "Field \"type\" specifying type of DataSource endpoint needs "
                        + "to be defined for JDBC Data Source in JSON");
    }
}