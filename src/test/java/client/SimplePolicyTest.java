package client;

import org.flywaydb.core.Flyway;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import server.EndToEndTest;

import java.nio.charset.StandardCharsets;
import java.sql.*;
import java.util.*;
import java.util.concurrent.ExecutionException;

public class SimplePolicyTest {
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
        System.out.println(sql);
        return sql.toString();
    }

    private String readSchemaSQL() throws Exception {
        java.net.URL url = EndToEndTest.class.getResource("/SimplePolicyTest/schema.sql");
        java.nio.file.Path resPath = java.nio.file.Paths.get(url.toURI());
        String sql = new String(java.nio.file.Files.readAllBytes(resPath), StandardCharsets.UTF_8);

        System.out.println(sql);
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
        java.net.URL url = EndToEndTest.class.getResource("/SimplePolicyTest/policies.sql");
        java.nio.file.Path resPath = java.nio.file.Paths.get(url.toURI());
        java.net.URL pk_url = EndToEndTest.class.getResource("/SimplePolicyTest/pk.txt");
        java.nio.file.Path pk_resPath = java.nio.file.Paths.get(pk_url.toURI());
        java.net.URL fk_url = EndToEndTest.class.getResource("/SimplePolicyTest/fk.txt");
        java.nio.file.Path fk_resPath = java.nio.file.Paths.get(fk_url.toURI());

        String dbFile = tempFolder.newFile("Db").getPath();
        String h2File = tempFolder.newFile("DbServer").getPath();
        String policyFile = tempFolder.newFile("policies.sql").getPath();
        String dbUrl = "jdbc:h2:" + dbFile;
        String h2Url = "jdbc:h2:" + h2File;
        proxyUrl = "jdbc:privacy:thin:" + resPath.toString() + "," + dbUrl + "," + h2Url + "," + pk_resPath.toString() + "," + fk_resPath.toString();

        Flyway flyway = new Flyway();
        flyway.setDataSource(dbUrl, dbUsername, dbPassword);
        flyway.migrate();

        setupTables(dbUrl, generateDBSQL(h2Url));
        setupTables(h2Url, readSchemaSQL());
    }

    private void runQuery(Connection conn, String query) throws Exception {
        PreparedStatement stmt = conn.prepareStatement(query);
        ResultSet s = stmt.executeQuery();
        s.close();
        stmt.close();
    }
    @Test
    public void runQueryGeneration() throws Exception {
        Class.forName("jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        // todo: data needs to be generated or we're querying an empty database
        for (int i = 0; i < 1; ++i) {
            runQuery(conn, "SELECT TABLE3.B, TABLE3.C, TABLE2.A, TABLE2.C, TABLE3.A, TABLE2.B, TABLE1.B, TABLE1.A FROM PUBLIC.TABLE3, PUBLIC.TABLE2, PUBLIC.TABLE1 WHERE TRUE AND TABLE3.A = TABLE1.A AND TABLE3.B = TABLE2.B AND (TABLE3.A = 8945 AND TABLE1.B = 9499)");
        }
    }

}
