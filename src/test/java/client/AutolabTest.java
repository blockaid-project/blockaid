package client;

import edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyConnection;
import org.apache.commons.io.FileUtils;
import org.flywaydb.core.Flyway;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.sql.*;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

import static com.google.common.base.Preconditions.checkNotNull;

public class AutolabTest {
    private static final String dbDatabaseName = "autolab_development";
    private static final String dbUrl = "jdbc:mysql://127.0.0.1:3306/" + dbDatabaseName +
            "?useSSL=false&useUnicode=true&character_set_server=utf8mb4&collation_server=utf8mb4_bin";
    private static final String dbUsername = "autolab";
    private static final String dbPassword = "12345678";
    private static final String resourcePath = "src/test/resources/AutolabTest";

    private static final String setupDbDir = checkNotNull(System.getenv("AUTOLAB_SETUP_PATH"));
    private static final String setupDbPath = setupDbDir + "/db";
    private static final String setupDbUrl = "jdbc:h2:" + setupDbPath;

    private String proxyUrl;

    @Before
    public void setupDb() throws Exception {
        {
            File dir = new File(setupDbDir);
            FileUtils.forceDelete(dir);
            FileUtils.forceMkdir(dir);
        }

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

    private void testQueries(String[] queries, int userId, int numRounds) throws ClassNotFoundException, SQLException {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
        try (PrivacyConnection conn = (PrivacyConnection) DriverManager.getConnection(proxyUrl, dbUsername, dbPassword)) {
            while (numRounds-- > 0) {
                try (Statement stmt = conn.createStatement()) {
                    stmt.execute("SET @_MY_UID = " + userId);
                }

                for (String q : queries) {
                    if (q.contains("%")) {
                        q = String.format(q, LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss.SSSSSS")));
                    }
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

    @Test
    public void testMyCourseSimple() throws ClassNotFoundException, SQLException {
        String[] queries = new String[]{
                "SELECT  `courses`.`id`, `courses`.`name` FROM `courses` WHERE `courses`.`name` = 'AutoPopulated' LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 52 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 52 AND `course_user_data`.`course_id` = 1 LIMIT 1",
                "SELECT  `courses`.`disabled` FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT `announcements`.* FROM `announcements` WHERE (start_date < '%1$s' AND end_date > '%1$s') AND `announcements`.`persistent` = 0 AND (`announcements`.`course_id` = 1 OR `announcements`.`system` = 1) ORDER BY `announcements`.`start_date` ASC",
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
                "SELECT  1 AS one FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'CategoryAutograde' AND (start_at < '%1$s') LIMIT 1",
                "SELECT `assessments`.* FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'CategoryAutograde' AND (start_at < '%1$s') ORDER BY due_at ASC, name ASC",
                "SELECT  1 AS one FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Homework' AND (start_at < '%1$s') LIMIT 1",
                "SELECT `assessments`.* FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Homework' AND (start_at < '%1$s') ORDER BY due_at ASC, name ASC",
                "SELECT  1 AS one FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Lab' AND (start_at < '%1$s') LIMIT 1",
                "SELECT `assessments`.* FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Lab' AND (start_at < '%1$s') ORDER BY due_at ASC, name ASC",
                "SELECT  1 AS one FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Quiz' AND (start_at < '%1$s') LIMIT 1",
                "SELECT `assessments`.* FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`category_name` = 'Quiz' AND (start_at < '%1$s') ORDER BY due_at ASC, name ASC",
                "SELECT  1 AS one FROM `attachments` WHERE `attachments`.`course_id` = 1 AND `attachments`.`released` = 1 LIMIT 1",
        };
        testQueries(queries, 52, 1);
    }

    @Test
    public void testMyCourseComplex() throws ClassNotFoundException, SQLException {
        String[] queries = new String[] {
                "SELECT `scheduler`.* FROM `scheduler` WHERE (`scheduler`.`next` < '%1$s')",
                "SELECT  `courses`.`id`, `courses`.`name` FROM `courses` WHERE `courses`.`name` = 'AutoPopulated' LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 2 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 2 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 2 AND `course_user_data`.`course_id` = 1 LIMIT 1",
                "SELECT  `courses`.`disabled` FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  1 AS one FROM `users` WHERE `users`.`email` = BINARY 'user0_autopopulated@foo.bar' AND `users`.`id` != 2 LIMIT 1",
                "SELECT `announcements`.* FROM `announcements` WHERE (start_date < '%1$s' AND end_date > '%1$s') AND `announcements`.`persistent` = 0 AND (`announcements`.`course_id` = 1 OR `announcements`.`system` = 1) ORDER BY `announcements`.`start_date` ASC",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 2 LIMIT 1 FOR UPDATE",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `assessments`.`id` FROM `assessments` WHERE `assessments`.`course_id` = 1 ORDER BY due_at DESC, name DESC LIMIT 1",
                "SELECT  `assessment_user_data`.* FROM `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = 4 AND `assessment_user_data`.`course_user_datum_id` = 2 LIMIT 1",
                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 37 LIMIT 1",

        };
        testQueries(queries, 2, 2);
    }

    @Test
    public void testMyCourseTime() throws ClassNotFoundException, SQLException {
        String[] queries = new String[] {
                "SELECT `scheduler`.* FROM `scheduler` WHERE (`scheduler`.`next` < '%1$s')",
                "SELECT  `courses`.`id`, `courses`.`name` FROM `courses` WHERE `courses`.`name` = 'AutoPopulated' LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 2 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 2 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 2 AND `course_user_data`.`course_id` = 1 LIMIT 1",
                "SELECT  `courses`.`disabled` FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`name` = 'homework3' LIMIT 1",
                "SELECT  `assessments`.* FROM `assessments` WHERE `assessments`.`id` = 4 LIMIT 1",
                "SELECT submissions.id AS submission_id, problems.id AS problem_id, scores.id AS score_id, scores.* FROM `submissions` JOIN problems ON" +
                        "        submissions.assessment_id = problems.assessment_id JOIN scores ON" +
                        "        (submissions.id = scores.submission_id" +
                        "        AND problems.id = scores.problem_id AND scores.released = 1) WHERE `submissions`.`assessment_id` = 4 AND `submissions`.`course_user_datum_id` = 2"
        };
        testQueries(queries, 2, 1);
    }
}
