package fatjdbc;

import fatjdbc.impl.PrivacyHandler;
import org.apache.calcite.avatica.AvaticaConnection;
import org.apache.calcite.avatica.BuiltInConnectionProperty;
import org.apache.calcite.avatica.ConnectionProperty;
import org.apache.calcite.avatica.DriverVersion;
import org.apache.calcite.avatica.Handler;
import org.apache.calcite.avatica.Meta;
import org.apache.calcite.avatica.UnregisteredDriver;
import org.apache.calcite.config.CalciteConnectionProperty;

import com.fasterxml.jackson.databind.ObjectMapper;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.sql.Connection;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Properties;

/**
 * Main class of Privacy JDBC driver.
 */
public class PrivacyDriver extends UnregisteredDriver {
    public static final String CONNECT_STRING_PREFIX = "jdbc:privacy:fat:";
    private static final String DB_SCHEMA_FACTORY = "catalog.db.SchemaFactory";
    private static final String DB_PREFIX = "db:";

    private static final String JSON_SCHEMA_FACTORY = "catalog.json.SchemaFactory";
    private static final String JSON_PREFIX = "json:";

    static {
        new PrivacyDriver().register();
    }

    public PrivacyDriver() {
        super();
    }

    @Override
    protected String getConnectStringPrefix() {
        return CONNECT_STRING_PREFIX;
    }

    @Override
    protected String getFactoryClassName(JdbcVersion jdbcVersion) {
        switch (jdbcVersion) {
            case JDBC_30:
            case JDBC_40:
                throw new IllegalArgumentException("JDBC version not supported: "
                        + jdbcVersion);
            case JDBC_41:
            default:
                return "fatjdbc.PrivacyJdbc41Factory";
        }
    }

    protected DriverVersion createDriverVersion() {
        return DriverVersion.load(
                PrivacyDriver.class,
                "org-apache-calcite-jdbc.properties",
                "Privacy JDBC Driver",
                "unknown version",
                "Privacy",
                "unknown version");
    }

    @Override
    protected Handler createHandler() {
        return new PrivacyHandler();
    }

    @Override
    protected Collection<ConnectionProperty> getConnectionProperties() {
        final List<ConnectionProperty> list = new ArrayList<ConnectionProperty>();
        Collections.addAll(list, BuiltInConnectionProperty.values());
        Collections.addAll(list, CalciteConnectionProperty.values());
        return list;
    }

    @Override
    public Meta createMeta(AvaticaConnection connection) {
        return new PrivacyMetaImpl((PrivacyConnectionImpl) connection,
                ((PrivacyConnectionImpl) connection).getProperties());
    }

    public Connection connect(String url, Properties info) throws SQLException {
        if (!acceptsURL(url)) {
            return null;
        }

        final String prefix = getConnectStringPrefix();
        final String urlSuffix = url.substring(prefix.length());

        if (urlSuffix.startsWith(DB_PREFIX)) {
            info.setProperty("schemaFactory",  DB_SCHEMA_FACTORY);
            final String path = urlSuffix.substring(DB_PREFIX.length());
            if (!path.isEmpty()) {
                try {
                    byte[] encoded = Files.readAllBytes(Paths.get(path));
                    ObjectMapper objectMapper = new ObjectMapper();
                    CatalogDetail catalogDetail = objectMapper.readValue(encoded, CatalogDetail.class);
                    info.setProperty("url", catalogDetail.dbCredentials.url);
                    info.setProperty("user", catalogDetail.dbCredentials.username);
                    info.setProperty("password", catalogDetail.dbCredentials.password);
                    info.setProperty("encryptionKey", catalogDetail.dbCredentials.encryptionKey);
                    info.setProperty("encrypt", catalogDetail.dbCredentials.encrypt);
                } catch (IOException e) {
                    throw new SQLException(e);
                }
            }
        } else if (urlSuffix.startsWith(JSON_PREFIX)) {
            info.setProperty("schemaFactory",  JSON_SCHEMA_FACTORY);
            final String path = urlSuffix.substring(JSON_PREFIX.length());
            if (!path.isEmpty()) {
                try {
                    byte[] encoded = Files.readAllBytes(Paths.get(path));
                    info.setProperty("model", new String(encoded, StandardCharsets.UTF_8));
                } catch (IOException e) {
                    throw new SQLException(e);
                }
            }
        } else {
            throw new SQLException("URL is malformed. Specify catalog type with 'db:' or 'json:'");
        }

        return super.connect(url, info);
    }
}
