package edu.berkeley.cs.netsys.privacy_proxy.jdbc;

import org.apache.calcite.avatica.DriverVersion;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.net.URI;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
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

        System.out.println("!!!\tPrivacyDriver.connect: " + url);


        // hack to read in primary/foreign keys from files, TODO read from schema instead
        // String[] urls = url.split(",", 4);
        String[] urls = url.split(",", 7);
        String policy_path = urls[0].substring(CONNECT_STRING_PREFIX.length());
        String deps_path = urls[1];
        String direct_schema_url = urls[2];
        String direct_access_url = urls[3];
        String pk_file = urls[4];
        String fk_file = urls[5];
        String database_name = urls.length >= 7 ? urls[6] : null;

        Connection direct_connection = DriverManager.getConnection(direct_access_url, info.getProperty("user"), info.getProperty("password"));
        Properties info_ = new Properties(info);
        info_.setProperty("url", direct_schema_url);
        if (database_name != null) {
            info_.setProperty("database_name", database_name);
        }
        try {
            info_.setProperty("policy", readFile(policy_path));
            info_.setProperty("deps", readFile(deps_path));
            info_.setProperty("pk", readFile(pk_file));
            info_.setProperty("fk", readFile(fk_file));
        } catch (IOException e) {
            throw new SQLException(e);
        }
        return new PrivacyConnection(direct_connection, info_);
    }

    private String readFile(String path) throws IOException {
        BufferedReader reader = new BufferedReader(new FileReader(path));
        List<String> lines = new ArrayList<>();
        String line = reader.readLine();
        StringBuilder current_line = new StringBuilder();
        while (line != null) {
            line = line.trim();
            if (line.length() > 0 && !line.startsWith("--")) {
                // remove semicolon
                if (line.endsWith(";")) {
                    line = line.substring(0, line.length() - 1);
                    current_line.append(line);
                    lines.add(current_line.toString());
                    current_line = new StringBuilder();
                } else {
                    current_line.append(line).append(' ');
                }
            }
            line = reader.readLine();
        }
        reader.close();
        assert current_line.toString().equals("");
        return String.join("\n", lines);
    }
}
