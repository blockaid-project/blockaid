package site.ycsb.db;

import jdbc.ThinClientUtil;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.Properties;

@Deprecated
public class PrivacyProxyConnection {
    private static int RETRIES = 5;
    private static int RETRY_DELAY = 2000;

    private PrivacyProxyConnection() {}

    public static Connection newConnection(String hostname, int port) throws ClassNotFoundException, SQLException {
        Class.forName("jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        for (int i = 0; i < RETRIES; ++i) {
            try {
                return DriverManager.getConnection(ThinClientUtil.getConnectionUrl(hostname, port), new Properties());
            } catch (RuntimeException e) {
                if (e.getMessage().contains("Connection refused")) {
                    try {
                        Thread.sleep(RETRY_DELAY);
                    } catch (InterruptedException e1) {
                        // do nothing
                    }
                } else {
                    throw e;
                }
            }
        }

        throw new RuntimeException("Failed to establish connection");
    }
}
