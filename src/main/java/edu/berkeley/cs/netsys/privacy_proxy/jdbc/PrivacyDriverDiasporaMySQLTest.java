package edu.berkeley.cs.netsys.privacy_proxy.jdbc;

import org.apache.commons.io.FileUtils;
import org.flywaydb.core.Flyway;

import java.io.File;
import java.io.IOException;
import java.sql.*;

public class PrivacyDriverDiasporaMySQLTest {
    private static final String dbDatabaseName = "diaspora_production";
    private static final String dbUrl = "jdbc:mysql://localhost:3306/" + dbDatabaseName +
            "?useSSL=false&useUnicode=true&character_set_server=utf8mb4&collation_server=utf8mb4_bin";
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

        System.out.println(proxyUrl);

        try (PrivacyConnection conn = (PrivacyConnection) DriverManager.getConnection(proxyUrl, dbUsername, dbPassword)) {
            for (int i = 0; i < 1; i++) {
                try (Statement stmt = conn.createStatement()) {
                    stmt.execute("SET @_MY_UID = 2");
                }

                {
                    final String query1 = "SELECT  `users`.* FROM `users` WHERE `users`.`id` = ? ORDER BY `users`.`id` ASC LIMIT ?";
                    try (PreparedStatement stmt = conn.prepareStatement(query1)) {
                        stmt.setInt(1, 2);
                        stmt.setInt(2, 1);
                        stmt.execute();
                        try (ResultSet rs = stmt.getResultSet()) {
                            while (rs.next()) {
                            }
                        }
                    }
                }

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
                    final String query3 = "SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = ? LIMIT ?";
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
//                    final String query4 = "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = ? AND `posts`.`author_id` = ? ORDER BY `posts`.`id` ASC LIMIT ?";
                    final String query4 = "(SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = ? AND `posts`.`author_id` = ?) UNION (SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = ? WHERE `posts`.`id` = ? AND `share_visibilities`.`user_id` = ?)";
                    try (PreparedStatement stmt = conn.prepareStatement(query4)) {
                        stmt.setInt(1, 4);
                        stmt.setInt(2, 3);
                        stmt.setString(3, "Post");
                        stmt.setInt(4, 4);
                        stmt.setInt(5, 2);
                        stmt.execute();
                        try (ResultSet rs = stmt.getResultSet()) {
                            while (rs.next()) {
                            }
                        }
                    }
                }

                {
                    final String query5 = "SELECT  profiles.id, profiles.diaspora_handle, profiles.first_name, profiles.last_name, profiles.image_url, profiles.image_url_small, profiles.image_url_medium, profiles.searchable, profiles.person_id, profiles.created_at, profiles.updated_at, profiles.full_name, profiles.nsfw, profiles.public_details FROM `profiles` WHERE `profiles`.`person_id` = ? LIMIT ?";
                    try (PreparedStatement stmt = conn.prepareStatement(query5)) {
                        stmt.setInt(1, 3);
                        stmt.setInt(2, 1);
                        stmt.execute();
                        try (ResultSet rs = stmt.getResultSet()) {
                            while (rs.next()) {
                            }
                        }
                    }
                }

                {
//                    final String query6 = "SELECT COUNT(*) FROM (SELECT DISTINCT photos.* FROM `photos` LEFT OUTER JOIN share_visibilities ON share_visibilities.shareable_id = photos.id AND share_visibilities.shareable_type = 'Photo' WHERE `photos`.`author_id` = ? AND (`share_visibilities`.`user_id` = 2 OR `photos`.`public` = 1) AND (photos.created_at < '2021-04-24 21:10:20.493711') AND `photos`.`pending` = ? ORDER BY photos.created_at DESC, created_at DESC) subquery_for_count";
                    final String query6 = "SELECT  `conversation_visibilities`.`id` AS t0_r0, `conversation_visibilities`.`conversation_id` AS t0_r1, `conversation_visibilities`.`person_id` AS t0_r2, `conversation_visibilities`.`unread` AS t0_r3, `conversation_visibilities`.`created_at` AS t0_r4, `conversation_visibilities`.`updated_at` AS t0_r5, `conversations`.`id` AS t1_r0, `conversations`.`subject` AS t1_r1, `conversations`.`guid` AS t1_r2, `conversations`.`author_id` AS t1_r3, `conversations`.`created_at` AS t1_r4, `conversations`.`updated_at` AS t1_r5 FROM `conversation_visibilities` LEFT OUTER JOIN `conversations` ON `conversations`.`id` = `conversation_visibilities`.`conversation_id` WHERE `conversation_visibilities`.`person_id` = ? ORDER BY conversations.updated_at DESC LIMIT ? OFFSET ?";
                    try (PreparedStatement stmt = conn.prepareStatement(query6)) {
                        stmt.setInt(1, 3);
                        stmt.setInt(2, 15);
                        stmt.setInt(3, 0);
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
