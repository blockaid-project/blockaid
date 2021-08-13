package client;

import edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyConnection;
import org.flywaydb.core.Flyway;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import server.EndToEndTest;

import java.io.File;
import java.sql.*;

public class AutolabTest {
    private static final String dbDatabaseName = "autolab_development";
    private static final String dbUrl = "jdbc:mysql://localhost:3306/" + dbDatabaseName +
            "?useSSL=false&useUnicode=true&character_set_server=utf8mb4&collation_server=utf8mb4_bin";
    private static final String dbUsername = "autolab";
    private static final String dbPassword = "12345678";
    private static final String resourcePath = "src/test/resources/AutolabTest";

    @Rule
    public TemporaryFolder tempFolder = new TemporaryFolder();

    private String proxyUrl;

    @Before
    public void setupDb() throws Exception {
        File setupDbFile = tempFolder.newFile("db");
        String setupDbUrl = "jdbc:h2:" + setupDbFile.getPath();

        Flyway flyway = new Flyway();
        flyway.setDataSource(setupDbUrl, dbUsername, dbPassword);
        flyway.migrate();

        Class.forName("org.h2.Driver");
        try (Connection conn = DriverManager.getConnection(setupDbUrl, dbUsername, dbPassword)) {
            try (Statement stmt = conn.createStatement()) {
                String sql = "INSERT INTO data_sources VALUES(1, 'MYSQL', '" + dbUrl + "',1,0,'CANONICAL','JDBC',NULL,NULL,NULL);\n" +
                        "INSERT INTO jdbc_sources VALUES(1, '" + dbUsername + "','" + dbPassword + "');\n" +
                        "UPDATE ds_sets SET default_datasource_id = 1 WHERE id = 1;\n";
                stmt.execute(sql);
            }
        }

        proxyUrl = String.format("jdbc:privacy:thin:%s,%s,%s,%s,%s,%s,%s",
                resourcePath + "/views.sql", // Policy file.
                resourcePath + "/deps.sql", // Misc dependencies.
                setupDbUrl,
                dbUrl,
                resourcePath + "/pk.txt", // Primary key dependencies.
                resourcePath + "/fk.txt", // Foreign key dependencies.
                dbDatabaseName
        );
    }

    @Test
    public void testMyCourse() throws ClassNotFoundException, SQLException {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");

        String[] queries = new String[]{
                "SELECT  `courses`.`id`, `courses`.`name` FROM `courses` WHERE `courses`.`name` = 'AutoPopulated' LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 52 ORDER BY `users`.`id` ASC LIMIT 1",
        };

        try (PrivacyConnection conn = (PrivacyConnection) DriverManager.getConnection(proxyUrl, dbUsername, dbPassword)) {
            try (Statement stmt = conn.createStatement()) {
                stmt.execute("SET @_MY_UID = 52");
            }

            for (String q : queries) {
                try (PreparedStatement stmt = conn.prepareStatement(q)) {
                    stmt.execute();
                    try (ResultSet rs = stmt.getResultSet()) {
                        while (rs.next()) {
                        }
                    }
                }
            }
        }
    }
}
