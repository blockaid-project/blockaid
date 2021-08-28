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
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

public class AutolabTest {
    private static final String dbDatabaseName = "autolab_development";
    private static final String dbUrl = "jdbc:mysql://127.0.0.1:3306/" + dbDatabaseName +
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
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 52 AND `course_user_data`.`course_id` = 1 LIMIT 1",
                "SELECT  `courses`.`disabled` FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",

                String.format(
                        "SELECT `announcements`.* FROM `announcements` " +
                                "WHERE (start_date < '%1$s' AND end_date > '%1$s') " +
                                "AND `announcements`.`persistent` = 0 " +
                                "AND (`announcements`.`course_id` = 1 OR `announcements`.`system` = 1) " +
                                "ORDER BY `announcements`.`start_date` ASC",
                        LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss.SSSSSS"))),

                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `assessments`.`id` FROM `assessments` WHERE `assessments`.`course_id` = 1 ORDER BY due_at DESC, name DESC LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 4 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 4 LIMIT 1",
                "SELECT `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`course_id` = 1 ORDER BY due_at ASC, name ASC",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 6 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 6 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 12 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 12 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 18 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 18 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 5 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 5 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 11 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 11 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 17 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 17 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 10 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 10 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 3 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 3 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 16 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 16 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 2 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 2 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 9 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 9 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 15 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 15 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 8 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 8 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 1 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 1 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 14 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 14 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 7 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 7 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 13 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 13 LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 19 AND `assessment_user_data`.`course_user_datum_id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 52 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`course_id` FROM `assessments` WHERE `assessments`.`id` = 19 LIMIT 1",
                "SELECT DISTINCT category_name FROM `assessments` WHERE `assessments`.`course_id` = 1",
                "SELECT  1 AS one FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'CategoryAutograde' AND (start_at < '2021-08-13 03:04:41.058711') LIMIT 1",
                "SELECT `assessments`.* FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'CategoryAutograde' AND (start_at < '2021-08-13 03:04:41.058711') ORDER BY due_at ASC, name ASC",
                "SELECT  1 AS one FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Homework' AND (start_at < '2021-08-13 03:04:41.067924') LIMIT 1",
                "SELECT `assessments`.* FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Homework' AND (start_at < '2021-08-13 03:04:41.067924') ORDER BY due_at ASC, name ASC",
                "SELECT  1 AS one FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Lab' AND (start_at < '2021-08-13 03:04:41.085304') LIMIT 1",
                "SELECT `assessments`.* FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Lab' AND (start_at < '2021-08-13 03:04:41.085304') ORDER BY due_at ASC, name ASC",
                "SELECT  1 AS one FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Quiz' AND (start_at < '2021-08-13 03:04:41.102801') LIMIT 1",
                "SELECT `assessments`.* FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Quiz' AND (start_at < '2021-08-13 03:04:41.102801') ORDER BY due_at ASC, name ASC",
                "SELECT  1 AS one FROM `attachments` WHERE `attachments`.`course_id` = 1 AND `attachments`.`released` = 1 LIMIT 1",
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
