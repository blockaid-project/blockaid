package edu.berkeley.cs.netsys.privacy_proxy.jdbc;

import org.apache.calcite.avatica.DriverVersion;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import static com.google.common.base.Preconditions.checkArgument;

/**
 * Privacy Driver for thin client
 */
public class PrivacyDriver extends org.apache.calcite.avatica.remote.Driver {
    public static final String CONNECT_STRING_PREFIX = "jdbc:privacy:thin:";

    private static final String policyFileName = "policies.sql";
    private static final String fkFileName = "fk.txt";
    private static final String pkFileName = "pk.txt";
    private static final String miscDepsFileName = "deps.sql";
    private static final String cacheEntriesFileName = "cache.txt";

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

        System.out.println("!!! PrivacyDriver.connect:");
        System.out.println("\t" + url);
        System.out.println("\t" + info);

        // hack to read in primary/foreign keys from files, TODO read from schema instead
        checkArgument(url.startsWith(CONNECT_STRING_PREFIX));
        String[] urls = url.substring(CONNECT_STRING_PREFIX.length()).split(",", 4);
        String policy_dir = urls[0];
        String direct_schema_url = urls[1];
        String direct_access_url = urls[2];
        String database_name = urls.length >= 4 ? urls[3] : null;

        try {
            if (direct_access_url.startsWith("jdbc:mysql:")) {
                Class.forName("com.mysql.jdbc.Driver");
            } else if (direct_access_url.startsWith("jdbc:h2:")) {
                Class.forName("org.h2.Driver");
            } else {
                throw new RuntimeException("unsupported direct connection: " + direct_access_url);
            }
        } catch (ClassNotFoundException e) {
            throw new RuntimeException(e);
        }

        Connection direct_connection = DriverManager.getConnection(direct_access_url, info.getProperty("user"), info.getProperty("password"));
        Properties info_ = new Properties(info);
        info_.setProperty("url", direct_schema_url);
        if (database_name != null) {
            info_.setProperty("database_name", database_name);
        }
        try {
            info_.setProperty("policy", readFile(Paths.get(policy_dir, policyFileName)));
            info_.setProperty("deps", readFile(Paths.get(policy_dir, miscDepsFileName)));
            info_.setProperty("pk", readFile(Paths.get(policy_dir, pkFileName)));
            info_.setProperty("fk", readFile(Paths.get(policy_dir, fkFileName)));
            info_.setProperty("cache_spec", readFile(Paths.get(policy_dir, cacheEntriesFileName), true));
        } catch (IOException e) {
            throw new SQLException(e);
        }
        return new PrivacyConnection(direct_connection, info_);
    }

    private String readFile(Path path, boolean optional) throws IOException {
        if (optional && !Files.exists(path)) {
            return "";
        }

        List<String> lines = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path)) {
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
        }
        return String.join("\n", lines);
    }

    private String readFile(Path path) throws IOException {
        return readFile(path, false);
    }
}
