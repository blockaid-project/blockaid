package client;

import edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyConnection;
import org.flywaydb.core.Flyway;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import policy_checker.QueryChecker;
import server.EndToEndTest;
import sql.QuerySequence;

import java.nio.charset.StandardCharsets;
import java.sql.*;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Properties;

import static org.junit.Assert.*;

public class DiasporaTest {
    private static String dbUsername = "sa";
    private static String dbPassword = "";

    private String proxyUrl;

    @Rule
    public TemporaryFolder tempFolder = new TemporaryFolder();

    private String generateDBSQL(String h2Url) {
        StringBuilder sql = new StringBuilder();
        // not escaped but oh well
        sql.append("INSERT INTO data_sources VALUES(1, 'H2', '").append(h2Url).append("',1,0,'CANONICAL','JDBC',NULL,NULL,NULL);\n");
        sql.append("INSERT INTO jdbc_sources VALUES(1, '").append(dbUsername).append("','").append(dbPassword).append("');\n");
        sql.append("UPDATE ds_sets SET default_datasource_id = 1 WHERE id = 1;\n");
        return sql.toString();
    }

    private String readSchemaSQL() throws Exception {
        java.net.URL url = EndToEndTest.class.getResource("/DiasporaTest/schema.sql");
        java.nio.file.Path resPath = java.nio.file.Paths.get(url.toURI());
        String sql = new String(java.nio.file.Files.readAllBytes(resPath), StandardCharsets.UTF_8);
        return sql;
    }

    private void setupTables(String dbUrl, String sql) throws ClassNotFoundException, SQLException {
        Class.forName("org.h2.Driver");

        Properties props = new Properties();
        props.setProperty("user", "sa");
        props.setProperty("password", "");

        Connection connection = DriverManager.getConnection(dbUrl, props);

        Statement stmt = connection.createStatement();
        stmt.execute(sql);
    }

    @Before
    public void setupDb() throws Exception {
        java.net.URL url = EndToEndTest.class.getResource("/DiasporaTest/policies.sql");
        java.nio.file.Path resPath = java.nio.file.Paths.get(url.toURI());
        java.net.URL pk_url = EndToEndTest.class.getResource("/DiasporaTest/pk.txt");
        java.nio.file.Path pk_resPath = java.nio.file.Paths.get(pk_url.toURI());
        java.net.URL fk_url = EndToEndTest.class.getResource("/DiasporaTest/fk.txt");
        java.nio.file.Path fk_resPath = java.nio.file.Paths.get(fk_url.toURI());
        java.net.URL deps_url = EndToEndTest.class.getResource("/DiasporaTest/deps.txt");
        java.nio.file.Path deps_resPath = java.nio.file.Paths.get(deps_url.toURI());

        String dbFile = tempFolder.newFile("Db").getPath();
        String h2File = tempFolder.newFile("DbServer").getPath();
        String dbUrl = "jdbc:h2:" + dbFile;
        String h2Url = "jdbc:h2:" + h2File;
        proxyUrl = "jdbc:privacy:thin:" + resPath.toString() + "," + deps_resPath.toString() + "," + dbUrl + "," + h2Url + "," + pk_resPath.toString() + "," + fk_resPath.toString();

        Flyway flyway = new Flyway();
        flyway.setDataSource(dbUrl, dbUsername, dbPassword);
        flyway.migrate();

        setupTables(dbUrl, generateDBSQL(h2Url));
        setupTables(h2Url, readSchemaSQL());
    }

    @Test
    public void runSimpleTest() throws Exception {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        // todo: data needs to be generated or we're querying an empty database

        String query = "SELECT username FROM users WHERE id = ?_MY_UID";
        PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
        p.setInt(1, 1);
        assertTrue(p.checkPolicy());
        p.addRow(Collections.singletonList("aaaa"));
        query = "SELECT username FROM users WHERE username = ??";
        p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
        p.setString(1, "aaaa");
        assertTrue(p.checkPolicy());
    }

    @Test
    public void runTestSetConst() throws Exception {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        try (PrivacyConnection conn =
                     (PrivacyConnection) DriverManager.getConnection(proxyUrl, dbUsername, dbPassword)) {
            conn.setAutoCommit(true);

            // todo: data needs to be generated or we're querying an empty database

            for (int i = 0; i < 3; i++) {
                try (Statement stmt = conn.createStatement()) {
                    stmt.execute("SET @_MY_UID = 2");
                }

                String query = "SELECT username FROM users WHERE id = 2";
                try (PrivacyConnection.PrivacyPreparedStatement p =
                             (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query)) {
                    assertTrue(p.checkPolicy());
                }
                conn.resetSequence();
            }
        }
    }

    @Test
    public void runSimpleTestWithData() throws Exception {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        String query = "INSERT INTO users(id, username) VALUES (??, ??)";
        PreparedStatement s = conn.prepareStatement(query);
        s.setInt(1, 1);
        s.setString(2, "aaaa");
        s.execute();

        for (int i = 0; i < 1; i++) {
            query = "SELECT username FROM users WHERE id = ?_MY_UID";
            PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
            p.setInt(1, 1);
            ResultSet resultSet = p.executeQuery();
            while (resultSet.next()) { /* do nothing */ }
            ((PrivacyConnection) conn).resetSequence();
        }

//        query = "SELECT username FROM users WHERE username = ??";
//        p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
//        p.setString(1, "aaaa");
//        resultSet = p.executeQuery();
//        while (resultSet.next()) { /* do nothing */ }
    }

    @Test
    public void testViewMyPost() throws Exception {
        Class.forName("jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        QueryChecker.ENABLE_CACHING = false;
        QueryChecker.ENABLE_PRECHECK = true;

        long startTime, endTime;
        startTime = System.nanoTime();

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        endTime = System.nanoTime();
        System.err.println("setup time: " + (endTime - startTime) / 1000000.0);
        startTime = System.nanoTime();

        String query = "INSERT INTO users(id, username) VALUES (??, ??)";
        PreparedStatement s = conn.prepareStatement(query);
        s.setInt(1, 1);
        s.setString(2, "aaaa");
        s.execute();

        endTime = System.nanoTime();
        System.err.println("data entry time: " + (endTime - startTime) / 1000000.0);

        List<Long> times = new ArrayList<>();
        for (int i = 0; i < 1000; ++i) {
            startTime = System.nanoTime();

            query = "SELECT users.id FROM users WHERE users.id = ?_MY_UID ORDER BY users.id ASC LIMIT 1";
            PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
            p.setInt(1, 1);

            endTime = System.nanoTime();
            System.err.println("query prepare time: " + (endTime - startTime) / 1000000.0);
            startTime = System.nanoTime();

            ResultSet resultSet = p.executeQuery();
            while (resultSet.next()) { /* do nothing */ }

            endTime = System.nanoTime();
            System.err.println("query run time: " + (endTime - startTime) / 1000000.0);
            times.add(endTime - startTime);

            ((PrivacyConnection) conn).resetSequence();
        }

        long y = 0;
        for (Long x : times) {
            y += x;
        }
        System.err.println("average query run time: " + (((float) y) / times.size()) / 1000000.0);
    }
}
