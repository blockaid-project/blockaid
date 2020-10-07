package jdbc;

import org.apache.calcite.avatica.DriverVersion;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.Properties;

/**
 * Privacy Driver for thin client
 */
public class PrivacyDriver extends org.apache.calcite.avatica.remote.Driver {

    public static final String CONNECT_STRING_PREFIX = "jdbc:privacy:thin:";

    static {
        new PrivacyDriver().register();
    }

    public PrivacyDriver() {
        super();
    }

    @Override
    protected DriverVersion createDriverVersion() {
        return DriverVersion.load(
                PrivacyDriver.class,
                "org-apache-calcite-jdbc.properties",
                "Privacy Thin Client JDBC PrivacyDriver",
                "unknown version",
                "Privacy",
                "unknown version");
    }

    @Override
    protected String getConnectStringPrefix() {
        return CONNECT_STRING_PREFIX;
    }

    @Override
    public Connection connect(String url, Properties info) throws SQLException {
        if (!this.acceptsURL(url)) {
            return null;
        }
        String[] urls = url.split(";", 2);

        String[] parts = urls[0].split(":");
        String hostname = parts[parts.length - 2];
        int port = Integer.parseInt(parts[parts.length - 1]);
        String proxy_url = ThinClientUtil.getConnectionUrl(hostname, port);
        String direct_url = urls[1];

        Connection direct_connection = DriverManager.getConnection(direct_url, info.getProperty("user"), info.getProperty("password"));
        return new PrivacyConnection(super.connect(proxy_url, info), direct_connection);
    }
}
