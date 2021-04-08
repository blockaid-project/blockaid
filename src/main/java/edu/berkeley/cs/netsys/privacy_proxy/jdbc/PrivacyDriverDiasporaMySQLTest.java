package edu.berkeley.cs.netsys.privacy_proxy.jdbc;

import org.apache.commons.io.FileUtils;
import org.flywaydb.core.Flyway;

import java.io.File;
import java.io.IOException;
import java.sql.*;

public class PrivacyDriverDiasporaMySQLTest {
    private static final String dbDatabaseName = "diaspora_development";
    private static final String dbUrl = "jdbc:mysql://localhost:3306/" + dbDatabaseName + "?useSSL=false";
    private static final String dbUsername = "diaspora";
    private static final String dbPassword = "12345678";

    private static final String setupDbDir = "/home/ubuntu/setup_db";
    private static final String setupDbPath = setupDbDir + "/db";
    private static final String setupDbUrl = "jdbc:h2:" + setupDbPath;
    // I think the setup DB is required to have the same username / password as the actual DB.

    private static void setUp() throws ClassNotFoundException, SQLException, IOException {
        {
            File dir = new File(setupDbDir);
            FileUtils.forceDelete(dir);
            FileUtils.forceMkdir(dir);
        }

        Flyway flyway = new Flyway();
        flyway.setDataSource(setupDbUrl, dbUsername, dbPassword);
        flyway.migrate();

        Class.forName("org.h2.Driver");
        Connection conn = DriverManager.getConnection(setupDbUrl, dbUsername, dbPassword);

        Statement stmt = conn.createStatement();
        String sql = "INSERT INTO data_sources VALUES(1, 'MYSQL', '" + dbUrl + "',1,0,'CANONICAL','JDBC',NULL,NULL,NULL);\n" +
                "INSERT INTO jdbc_sources VALUES(1, '" + dbUsername + "','" + dbPassword + "');\n" +
                "UPDATE ds_sets SET default_datasource_id = 1 WHERE id = 1;\n";
        stmt.execute(sql);

        stmt.close();
        conn.close();
    }

    private static void runSimpleTest() throws ClassNotFoundException, SQLException {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");
        Class.forName("com.mysql.jdbc.Driver");

        String proxyUrl = String.format("jdbc:privacy:thin:%s,%s,%s,%s,%s,%s,%s",
                "/home/ubuntu/diaspora/policy/policies.sql", // Policy file.
                "/home/ubuntu/diaspora/policy/deps.txt", // Misc dependencies.
                setupDbUrl,
                dbUrl,
                "/home/ubuntu/diaspora/policy/pk.txt", // Primary key dependencies.
                "/home/ubuntu/diaspora/policy/fk.txt", // Foreign key dependencies.
                dbDatabaseName
        );

        try (PrivacyConnection conn = (PrivacyConnection) DriverManager.getConnection(proxyUrl, dbUsername, dbPassword)) {
            for (int i = 0; i < 2; i++) {
                String username = null;

                final String query1 = "SELECT users.* FROM users WHERE id = ?_MY_UID";
                System.out.println(query1);
                try (PrivacyConnection.PrivacyPreparedStatement stmt =
                             (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query1)) {
                    stmt.setInt(1, 1);
                    try (ResultSet rs = stmt.executeQuery()) {
                        while (rs.next()) {
                            username = rs.getString("username");
                            System.out.println("\tusername:\t" + username);
                        }
                    }
                }

                if (username == null) {
                    System.out.println("\tFAILED: query returned empty");
                    return;
                }

//                String query2 = "SELECT email FROM users WHERE username = ??";
//                System.out.println(query2);
//                try (PrivacyConnection.PrivacyPreparedStatement stmt =
//                             (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query2)) {
//                    stmt.setString(1, username);
//                    try (ResultSet rs = stmt.executeQuery()) {
//                        while (rs.next()) {
//                            System.out.println("\temail:\t" + rs.getString("email"));
//                        }
//                    } catch (SQLException ex) {
//                        System.out.println("\tFAILED:\t" + ex);
//                    }
//                }
//
//                System.out.println();

                conn.resetSequence();
            }
        }
    }

    public static void main(String[] args) throws Exception {
        switch (args[0]) {
            case "setup":
                setUp();
                break;
            case "test":
                runSimpleTest();
                break;
            default:
                System.err.println("invalid command line");
                break;
        }
    }
}
