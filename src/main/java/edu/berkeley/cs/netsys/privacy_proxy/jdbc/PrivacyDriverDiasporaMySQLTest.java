package edu.berkeley.cs.netsys.privacy_proxy.jdbc;

import org.apache.commons.io.FileUtils;
import org.flywaydb.core.Flyway;

import java.io.File;
import java.io.IOException;
import java.sql.*;

public class PrivacyDriverDiasporaMySQLTest {
    private static final String dbDatabaseName = "diaspora_production";
    private static final String dbUrl = "jdbc:mysql://diaspora.internal:3306/" + dbDatabaseName +
            "?useSSL=false&useUnicode=true&character_set_server=utf8mb4&collation_server=utf8mb4_bin";
    private static final String dbUsername = "diaspora";
    private static final String dbPassword = "12345678";

    private static final String setupDbDir = "/Users/zhangwen/scratch/setup_db";
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
                "/Users/zhangwen/code/diaspora/policy/policies.sql", // Policy file.
                "/Users/zhangwen/code/diaspora/policy/deps.txt", // Misc dependencies.
                setupDbUrl,
                dbUrl,
                "/Users/zhangwen/code/diaspora/policy/pk.txt", // Primary key dependencies.
                "/Users/zhangwen/code/diaspora/policy/fk.txt", // Foreign key dependencies.
                dbDatabaseName
        );

        System.out.println(proxyUrl);

        try (PrivacyConnection conn = (PrivacyConnection) DriverManager.getConnection(proxyUrl, dbUsername, dbPassword)) {
            for (int i = 0; i < 1; i++) {
//                try (Statement stmt = conn.createStatement()) {
//                    stmt.execute("SET @_MY_UID = 2");
//                }

//                {
//                    final String query1 = "SELECT  `users`.* FROM `users` WHERE `users`.`id` = ?_MY_UID ORDER BY `users`.`id` ASC LIMIT ?";
//                    try (PreparedStatement stmt = conn.prepareStatement(query1)) {
//                        stmt.setInt(1, 2);
//                        stmt.setInt(2, 1);
//                        stmt.execute();
//                        try (ResultSet rs = stmt.getResultSet()) {
//                            while (rs.next()) {
//                            }
//                        }
//                    }
//                }

//                {
//                    final String query2 = "SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = ? WHERE `posts`.`id` = ? AND `share_visibilities`.`user_id` = ?";
//                    try (PreparedStatement stmt = conn.prepareStatement(query2)) {
//                        stmt.setString(1, "Post");
//                        stmt.setInt(2, 4);
//                        stmt.setInt(3, 2);
//                        stmt.execute();
//                        try (ResultSet rs = stmt.getResultSet()) {
//                            while (rs.next()) {
//                            }
//                        }
//                    }
//                }

                {
                    final String query3 = "SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = ?_MY_UID LIMIT ?";
                    try (PreparedStatement stmt = conn.prepareStatement(query3)) {
                        stmt.setInt(1, 2);
                        stmt.setInt(2, 1);
                        stmt.execute();
                        try (ResultSet rs = stmt.getResultSet()) {
                            while (rs.next()) {
                            }
                        }
                    }
                }

                {
//                    final String query4 = "(SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = ? AND `posts`.`author_id` = ?) UNION (SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = ? WHERE `posts`.`id` = ? AND `share_visibilities`.`user_id` = ?)";
                    final String query4 = "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = ? AND `posts`.`author_id` = ?";
                    try (PreparedStatement stmt = conn.prepareStatement(query4)) {
                        stmt.setInt(1, 4);
                        stmt.setInt(2, 3);
//                        stmt.setString(3, "Post");
//                        stmt.setInt(4, 4);
//                        stmt.setInt(5, 2);
                        stmt.execute();
                        try (ResultSet rs = stmt.getResultSet()) {
                            while (rs.next()) {
                            }
                        }
                    }
                }

                {
                    final String query5 = "SELECT  `notifications`.* FROM `notifications` WHERE `notifications`.`recipient_id` = ? ORDER BY updated_at desc LIMIT ?";
                    try (PreparedStatement stmt = conn.prepareStatement(query5)) {
                        stmt.setInt(1, 2);
                        stmt.setInt(2, 10);
                        stmt.execute();
                        try (ResultSet rs = stmt.getResultSet()) {
                            while (rs.next()) {
                                System.out.println("\t" + rs.getString(2) + ", " + rs.getInt(3));
                            }
                        }
                    }
                }

                {
//                    final String query6 = "SELECT `posts`.* FROM `posts` WHERE `posts`.`id` IN (?, ?, ?)";
                    final String query6 = "SELECT `posts`.* FROM `posts` WHERE `posts`.`id` = 42";
                    try (PreparedStatement stmt = conn.prepareStatement(query6)) {
//                        stmt.setInt(1, 42);
//                        stmt.setInt(2, 10);
//                        stmt.setInt(3, 2);
                        stmt.execute();
                        try (ResultSet rs = stmt.getResultSet()) {
                            while (rs.next()) {
                            }
                        }
                    }
                }

                conn.resetSequence();
            }
        }
    }
    private static void runAdminTest() throws ClassNotFoundException, SQLException {
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

        System.out.println(proxyUrl);

        try (PrivacyConnection conn = (PrivacyConnection) DriverManager.getConnection(proxyUrl, dbUsername, dbPassword)) {
            for (int i = 0; i < 1; i++) {
                try (Statement stmt = conn.createStatement()) {
                    stmt.execute("SET @_MY_UID = 2");
                }

                {
                    final String query1 = "SELECT  people.* FROM people WHERE people.owner_id = ?";
                    try (PreparedStatement stmt = conn.prepareStatement(query1)) {
                        stmt.setInt(1, 2);
                        stmt.execute();
                        try (ResultSet rs = stmt.getResultSet()) {
                            while (rs.next()) {
                            }
                        }
                    }
                }

                {
                    final String query1 = "SELECT  1 AS one FROM roles WHERE roles.person_id = ? AND roles.name IN ('admin', 'moderator')";
                    try (PreparedStatement stmt = conn.prepareStatement(query1)) {
                        stmt.setInt(1, 3);
                        stmt.execute();
                        try (ResultSet rs = stmt.getResultSet()) {
                            while (rs.next()) {
                            }
                        }
                    }
                }

                {
                    final String query5 = "SELECT * FROM reports";
                    try (PreparedStatement stmt = conn.prepareStatement(query5)) {
                        stmt.execute();
                        try (ResultSet rs = stmt.getResultSet()) {
                            while (rs.next()) {
                            }
                        }
                    }
                }

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
            case "adminTest":
                runAdminTest();
                break;
            default:
                System.err.println("invalid command line");
                break;
        }
    }
}
