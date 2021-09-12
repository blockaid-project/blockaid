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
    private static final String dbDatabaseName = "autolab_production_mod";
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

        proxyUrl = String.format("jdbc:privacy:thin:%s,%s,%s,%s",
                resourcePath,
                setupDbUrl,
                dbUrl,
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
                    if (q.startsWith("SELECT")) {
                        try (PreparedStatement stmt = conn.prepareStatement(q)) {
                            stmt.execute();
                            try (ResultSet rs = stmt.getResultSet()) {
                                while (rs.next()) {
                                }
                            }
                        }
                    } else {
                        try (Statement stmt = conn.createStatement()) {
                            stmt.execute(q);
                        }
                    }
                }

                try (Statement stmt = conn.createStatement()) {
                    stmt.execute("SET @TRACE = null");
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
    public void testMyAssessmentComplex() throws ClassNotFoundException, SQLException {
        String[] queries = new String[] {
                "SELECT `scheduler`.* FROM `scheduler` WHERE (`scheduler`.`next` < '%1$s')",
                "SELECT  `courses`.`id`, `courses`.`name` FROM `courses` WHERE `courses`.`name` = 'AutoPopulated' LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 2 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 2 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 2 AND `course_user_data`.`course_id` = 1 LIMIT 1",
                "SELECT  `courses`.`disabled` FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`," +
                        " `assessments`.`start_at`, `assessments`.`name`, `assessments`.`course_id`," +
                        " `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name`" +
                        " FROM `assessments` WHERE `assessments`.`course_id` = 1 AND" +
                        " `assessments`.`name` = 'homework3' LIMIT 1",
                "SELECT `assessments`.* FROM `assessments` WHERE `assessments`.`id` = 4",
                // FIXME(zhangwen): finish this trace.
        };
        testQueries(queries, 2, 1);
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

    @Test
    public void testCAShowQuiz() throws ClassNotFoundException, SQLException {
        String[] queries = new String[] {
                "SELECT `scheduler`.* FROM `scheduler` WHERE `scheduler`.`next` < '%1$s'",
                "SELECT  `courses`.`id`, `courses`.`name` FROM `courses` WHERE `courses`.`name` = 'AutoPopulated' LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 52 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 52 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 52 AND `course_user_data`.`course_id` = 1 LIMIT 1",
                "SELECT  `courses`.`disabled` FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`name` = 'quiz0' LIMIT 1",
                "SELECT `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`course_id` = 1",
                "SELECT `assessment_user_data`.* FROM `assessment_user_data` INNER JOIN `assessments` ON `assessment_user_data`.`assessment_id` = `assessments`.`id` WHERE `assessments`.`course_id` = 1 AND `assessment_user_data`.`assessment_id` = 13",
//                "SELECT `submissions`.* FROM `submissions` INNER JOIN `assessment_user_data` ON `assessment_user_data`.`latest_submission_id` = `submissions`.`id` INNER JOIN `course_user_data` ON `course_user_data`.`id` = `submissions`.`course_user_datum_id` WHERE `submissions`.`assessment_id` = 13 AND `course_user_data`.`course_id` = 1",
//                "SELECT `scores`.* FROM `scores` INNER JOIN `submissions` ON `submissions`.`id` = `scores`.`submission_id` INNER JOIN `assessment_user_data` ON `assessment_user_data`.`latest_submission_id` = `submissions`.`id` WHERE `submissions`.`ignored` = 0 AND `submissions`.`assessment_id` = 13",
//                "SELECT `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = 1 ORDER BY due_at ASC, name ASC",
//                "SELECT `problems`.* FROM `problems` WHERE `problems`.`assessment_id` = 13",
//                "SELECT `users`.`id`, `users`.`first_name`, `users`.`last_name`, `users`.`email`, `users`.`school`, `users`.`major`, `users`.`year` FROM `users`  WHERE `users`.`id` = 1 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 22 LIMIT 1 FOR UPDATE",
//                "SELECT  `assessments`.* FROM `assessments` WHERE `assessments`.`id` = 13 LIMIT 1",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 2 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 50 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 3 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 95 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 4 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 138 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 5 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 176 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 6 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 216 LIMIT 1 FOR UPDATE",
//                "SELECT  `extensions`.* FROM `extensions` WHERE `extensions`.`course_user_datum_id` = 6 AND `extensions`.`assessment_id` = 13 LIMIT 1",
//                "SELECT  `score_adjustments`.* FROM `score_adjustments` WHERE `score_adjustments`.`type` IN ('Penalty') AND `score_adjustments`.`id` = 1 LIMIT 1",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 7 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 256 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 8 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 292 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 9 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 330 LIMIT 1 FOR UPDATE",
//                "SELECT  `extensions`.* FROM `extensions` WHERE `extensions`.`course_user_datum_id` = 9 AND `extensions`.`assessment_id` = 13 LIMIT 1",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 10 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 369 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 11 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 401 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 12 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 434 LIMIT 1 FOR UPDATE",
//                "SELECT  `extensions`.* FROM `extensions` WHERE `extensions`.`course_user_datum_id` = 12 AND `extensions`.`assessment_id` = 13 LIMIT 1",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 13 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 471 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 14 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 508 LIMIT 1 FOR UPDATE",
//                "SELECT  `extensions`.* FROM `extensions` WHERE `extensions`.`course_user_datum_id` = 14 AND `extensions`.`assessment_id` = 13 LIMIT 1",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 15 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 543 LIMIT 1 FOR UPDATE",
//                "SELECT  `extensions`.* FROM `extensions` WHERE `extensions`.`course_user_datum_id` = 15 AND `extensions`.`assessment_id` = 13 LIMIT 1",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 16 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 569 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 17 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 605 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 18 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 639 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 19 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 670 LIMIT 1 FOR UPDATE",
//                "SELECT  `extensions`.* FROM `extensions` WHERE `extensions`.`course_user_datum_id` = 19 AND `extensions`.`assessment_id` = 13 LIMIT 1",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 20 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 705 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 21 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 737 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 22 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 778 LIMIT 1 FOR UPDATE",
//                "SELECT  `extensions`.* FROM `extensions` WHERE `extensions`.`course_user_datum_id` = 22 AND `extensions`.`assessment_id` = 13 LIMIT 1",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 23 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 811 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 24 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 843 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 25 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 881 LIMIT 1 FOR UPDATE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 26 LIMIT 1",
//                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 919 LIMIT 1 FOR UPDATE",
//                "SELECT `announcements`.* FROM `announcements` WHERE `announcements`.`persistent` = 1 AND (`announcements`.`course_id` = 1 OR `announcements`.`system` = 1)",
        };
        testQueries(queries, 52, 1);
    }

    @Test
    public void testProductionUser0Course0() throws ClassNotFoundException, SQLException {
        String[] queries = new String[] {
                "SELECT `scheduler`.* FROM `scheduler` WHERE `scheduler`.`next` < '2021-09-10 05:20:17'",
                "SELECT  `courses`.`id`, `courses`.`name` FROM `courses` WHERE `courses`.`name` = 'Course0' LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 1 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 1 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 1 AND `course_user_data`.`course_id` = 1 LIMIT 1",
                "SELECT  `courses`.`disabled` FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`name` = 'quiz4' LIMIT 1",
                "SELECT COUNT(`submissions`.`id`) FROM `submissions` WHERE `submissions`.`assessment_id` = 17 AND `submissions`.`course_user_datum_id` = 1",
        };
        testQueries(queries, 1, 1);
    }

    @Test
    public void testProductionDownload() throws ClassNotFoundException, SQLException {
        String[] queries = new String[] {
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 1 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  `courses`.`id`, `courses`.`name` FROM `courses` WHERE `courses`.`name` = 'Course0' LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 1 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 1 AND `course_user_data`.`course_id` = 1 LIMIT 1",
                "SELECT  `courses`.`disabled` FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 1 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = 1 AND `assessments`.`name` = 'quiz4' LIMIT 1",
                "SELECT  1 AS one FROM `submissions` WHERE `submissions`.`assessment_id` = 17 AND `submissions`.`id` = 33 LIMIT 1",
                "SELECT  `submissions`.`id`, `submissions`.`version`, `submissions`.`course_user_datum_id`, `submissions`.`assessment_id`, `submissions`.`filename`, `submissions`.`created_at`, `submissions`.`updated_at`, `submissions`.`notes`, `submissions`.`mime_type`, `submissions`.`special_type`, `submissions`.`submitted_by_id`, `submissions`.`autoresult`, `submissions`.`detected_mime_type`, `submissions`.`submitter_ip`, `submissions`.`tweak_id`, `submissions`.`ignored`, `submissions`.`dave`, `submissions`.`settings`, `submissions`.`embedded_quiz_form_answer`, `submissions`.`submitted_by_app_id` FROM `submissions` WHERE `submissions`.`assessment_id` = 17 AND `submissions`.`id` = 33 AND `submissions`.`course_user_datum_id` = 1 LIMIT 1",
                "SELECT  `assessments`.* FROM `assessments` WHERE `assessments`.`id` = 17 LIMIT 1",
                "SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = 33 LIMIT 1",
        };
        testQueries(queries, 1, 1);
    }

    @Test
    public void testProductionShowQuiz() throws ClassNotFoundException, SQLException {
        String[] queries = new String[]{
                "SELECT `scheduler`.* FROM `scheduler` WHERE `scheduler`.`next` < '%1$s'",
                "SELECT  `courses`.`id`, `courses`.`name` FROM `courses` WHERE `courses`.`name` = 'Course0' LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 27000050 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 27000050 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 27000050 AND `course_user_data`.`course_id` = 10000000 LIMIT 1",
                "SELECT  `courses`.`disabled` FROM `courses` WHERE `courses`.`id` = 10000000 LIMIT 1",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 10000000 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = 10000000 AND `assessments`.`name` = 'quiz4' LIMIT 1",
                "SELECT `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`course_id` = 10000000",
                "SELECT `assessment_user_data`.* FROM `assessment_user_data` INNER JOIN `assessments` ON `assessment_user_data`.`assessment_id` = `assessments`.`id` WHERE `assessments`.`course_id` = 10000000",
                "SELECT `submissions`.* FROM `submissions` INNER JOIN `assessment_user_data` ON `assessment_user_data`.`latest_submission_id` = `submissions`.`id` INNER JOIN `course_user_data` ON `course_user_data`.`id` = `submissions`.`course_user_datum_id` INNER JOIN `assessments` ON `submissions`.`assessment_id` = `assessments`.`id` WHERE `assessments`.`course_id` = 10000000 AND `submissions`.`assessment_id` = 5000016",
                "CHECK CACHE READ foo"
        };
        testQueries(queries, 27000050, 1);
    }
}
