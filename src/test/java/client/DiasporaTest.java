package client;

import jdbc.PrivacyConnection;
import org.flywaydb.core.Flyway;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import server.EndToEndTest;

import java.nio.charset.StandardCharsets;
import java.sql.*;
import java.util.Collections;
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
        Class.forName("jdbc.PrivacyDriver");
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
    public void runSimpleTestWithData() throws Exception {
        Class.forName("jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        String query = "INSERT INTO users(id, username) VALUES (??, ??)";
        PreparedStatement s = conn.prepareStatement(query);
        s.setInt(1, 1);
        s.setString(2, "aaaa");
        s.execute();

        query = "SELECT username FROM users WHERE id = ?_MY_UID";
        PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
        p.setInt(1, 1);
        ResultSet resultSet = p.executeQuery();
        while (resultSet.next()) { /* do nothing */ }

        query = "SELECT username FROM users WHERE username = ??";
        p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
        p.setString(1, "aaaa");
        resultSet = p.executeQuery();
        while (resultSet.next()) { /* do nothing */ }
    }

}
