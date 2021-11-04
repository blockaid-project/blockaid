package client;

import edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyConnection;
import org.apache.calcite.avatica.util.Casing;
import org.apache.calcite.jdbc.CalciteConnection;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.Planner;
import org.apache.calcite.tools.ValidationException;
import org.apache.calcite.util.Pair;
import org.junit.Before;
import org.junit.Test;
import org.apache.calcite.adapter.jdbc.JdbcSchema;

import java.sql.*;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.Arrays;
import java.util.Properties;

import static com.google.common.base.Preconditions.checkArgument;

public class AutolabTest {
    private static final String dbDatabaseName = "autolab_production_mod";
    private static final String dbUrl = "jdbc:mysql://127.0.0.1:3306/" + dbDatabaseName +
            "?useSSL=false&useUnicode=true&character_set_server=utf8mb4&collation_server=utf8mb4_bin";
    private static final String dbUsername = "autolab";
    private static final String dbPassword = "12345678";
    private static final String resourcePath = "src/test/resources/AutolabTest";

    private String proxyUrl;

    @Before
    public void setupDb() throws Exception {
        proxyUrl = String.format("jdbc:privacy:thin:%s,%s,%s",
                resourcePath,
                dbUrl,
                dbDatabaseName
        );
    }

    private void testQueries(String[] queries, int userId, int numRounds) throws ClassNotFoundException, SQLException {
        testQueries(
                Arrays.stream(queries).map(PQuery::new).toArray(PQuery[]::new),
                userId, numRounds
        );
    }

    private void testQueries(PQuery[] queries, int userId, int numRounds) throws ClassNotFoundException, SQLException {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
        try (PrivacyConnection conn = (PrivacyConnection) DriverManager.getConnection(proxyUrl, dbUsername, dbPassword)) {
            while (numRounds-- > 0) {
                long startMs = System.currentTimeMillis();
                try (Statement stmt = conn.createStatement()) {
                    stmt.execute("SET @_MY_UID = " + userId);
                }

                for (PQuery pq : queries) {
                    String q = pq.query;
                    if (q.contains("%")) {
                        q = String.format(q, LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss.SSSSSS")));
                    }
                    if (q.startsWith("SELECT")) {
                        try (PreparedStatement stmt = conn.prepareStatement(q)) {
                            for (int i = 1; i <= pq.params.length; ++i) {
                                Object o = pq.params[i - 1];
                                if (o instanceof Integer integer) {
                                    stmt.setInt(i, integer);
                                } else if (o instanceof String str) {
                                    stmt.setString(i, str);
                                } else if (o instanceof Boolean b) {
                                    stmt.setBoolean(i, b);
                                } else {
                                    throw new UnsupportedOperationException("unsupported param: " + o);
                                }
                            }
                            stmt.execute();
                            try (ResultSet rs = stmt.getResultSet()) {
                                while (rs.next()) {
                                }
                            }
                        }
                    } else {
                        checkArgument(pq.params.length == 0);
                        try (Statement stmt = conn.createStatement()) {
                            stmt.execute(q);
                        }
                    }
                }

                try (Statement stmt = conn.createStatement()) {
                    stmt.execute("SET @TRACE = null");
                }
//                System.out.println("round:\t" + (System.currentTimeMillis() - startMs));
            }
        }
    }

    @Test
    public void testProductionAllCourses() throws ClassNotFoundException, SQLException {
        String[] queries = new String[]{
                "SELECT `scheduler`.* FROM `scheduler` WHERE `scheduler`.`next` < '%1$s'",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 27000000 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  1 AS one FROM `courses` INNER JOIN `course_user_data` ON `courses`.`id` = `course_user_data`.`course_id` WHERE `course_user_data`.`user_id` = 27000000 LIMIT 1",
                "SELECT `courses`.`id`, `courses`.`name`, `courses`.`display_name`, `courses`.`start_date`, `courses`.`end_date`, `courses`.`disabled`, `courses`.`semester` FROM `courses` INNER JOIN `course_user_data` ON `courses`.`id` = `course_user_data`.`course_id` WHERE `course_user_data`.`user_id` = 27000000 ORDER BY display_name ASC",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 27000000 LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 27000000 AND `course_user_data`.`course_id` = 10000000 LIMIT 1",
                "SELECT  `users`.`id`, `users`.`first_name`, `users`.`last_name`, `users`.`email`, `users`.`school`, `users`.`major`, `users`.`year`, `users`.`administrator` FROM `users` WHERE `users`.`id` = 27000000 LIMIT 1",
                "SELECT `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = 10000000 AND (start_at < '%1$s' AND end_at > '%1$s') ORDER BY due_at ASC, name ASC",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 27000000 AND `course_user_data`.`course_id` = 10000001 LIMIT 1",
                "SELECT `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = 10000001 AND (start_at < '%1$s' AND end_at > '%1$s') ORDER BY due_at ASC, name ASC",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 27000000 AND `course_user_data`.`course_id` = 10000002 LIMIT 1",
                "SELECT `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = 10000002 AND (start_at < '%1$s' AND end_at > '%1$s') ORDER BY due_at ASC, name ASC",
        };
        testQueries(queries, 27000000, 10000);
    }

    @Test
    public void testProductionShowQuizPartial() throws ClassNotFoundException, SQLException {
        String[] queries = new String[]{
                "SELECT `scheduler`.* FROM `scheduler` WHERE `scheduler`.`next` < '2021-09-12 23:14:07'",
                "SELECT  `courses`.`id`, `courses`.`name` FROM `courses` WHERE `courses`.`name` = 'Course0' LIMIT 1",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 27000000 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = 27000000 AND `course_user_data`.`course_id` = 10000000 LIMIT 1",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 10000000 AND `courses`.`disabled` = 0 LIMIT 1",
                "SELECT  `users`.`id`, `users`.`first_name`, `users`.`last_name`, `users`.`email`, `users`.`school`, `users`.`major`, `users`.`year`, `users`.`administrator` FROM `users` WHERE `users`.`id` = 27000000 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = 10000000 AND `assessments`.`name` = 'quiz4' LIMIT 1",
                "SELECT COUNT(`submissions`.`id`) FROM `submissions` WHERE `submissions`.`assessment_id` = 5000016 AND `submissions`.`course_user_datum_id` = 9000000",
                "SELECT `assessments`.* FROM `assessments` WHERE `assessments`.`id` = 5000016",
                "SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`id` = 9000000 LIMIT 1",
                "SELECT  `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`id` = 5000016 LIMIT 1",
                "SELECT  `courses`.* FROM `courses` WHERE `courses`.`id` = 10000000 LIMIT 1",
                "SELECT  `extensions`.* FROM `extensions` WHERE `extensions`.`course_user_datum_id` = 9000000 AND `extensions`.`assessment_id` = 5000016 LIMIT 1",
                "SELECT  `extensions`.* FROM `extensions` WHERE `extensions`.`assessment_id` = 5000016 AND `extensions`.`course_user_datum_id` = 9000000 LIMIT 1",
                "SELECT `submissions`.`id`, `submissions`.`version`, `submissions`.`course_user_datum_id`, `submissions`.`assessment_id`, `submissions`.`filename`, `submissions`.`created_at`, `submissions`.`updated_at`, `submissions`.`notes`, `submissions`.`mime_type`, `submissions`.`special_type`, `submissions`.`submitted_by_id`, `submissions`.`autoresult`, `submissions`.`detected_mime_type`, `submissions`.`submitter_ip`, `submissions`.`tweak_id`, `submissions`.`ignored`, `submissions`.`dave`, `submissions`.`settings`, `submissions`.`embedded_quiz_form_answer`, `submissions`.`submitted_by_app_id`, submissions.id AS submission_id, problems.id AS problem_id, scores.id AS score_id, scores.* FROM `submissions` JOIN problems ON submissions.assessment_id = problems.assessment_id JOIN scores ON (submissions.id = scores.submission_id AND problems.id = scores.problem_id AND scores.released = 1) WHERE `submissions`.`assessment_id` = 5000016 AND `submissions`.`course_user_datum_id` = 9000000 ORDER BY version DESC",
                "SELECT  `scoreboards`.* FROM `scoreboards` WHERE `scoreboards`.`assessment_id` = 5000016 LIMIT 1",
                "SELECT COUNT(*) FROM `submissions` WHERE `submissions`.`assessment_id` = 5000016 AND `submissions`.`course_user_datum_id` = 9000000",
                "SELECT `attachments`.* FROM `attachments` WHERE `attachments`.`assessment_id` = 5000016",
                "SELECT  `submissions`.`id`, `submissions`.`version`, `submissions`.`course_user_datum_id`, `submissions`.`assessment_id`, `submissions`.`filename`, `submissions`.`created_at`, `submissions`.`updated_at`, `submissions`.`notes`, `submissions`.`mime_type`, `submissions`.`special_type`, `submissions`.`submitted_by_id`, `submissions`.`autoresult`, `submissions`.`detected_mime_type`, `submissions`.`submitter_ip`, `submissions`.`tweak_id`, `submissions`.`ignored`, `submissions`.`dave`, `submissions`.`settings`, `submissions`.`embedded_quiz_form_answer`, `submissions`.`submitted_by_app_id` FROM `submissions` WHERE `submissions`.`assessment_id` = 5000016 AND `submissions`.`course_user_datum_id` = 9000000 ORDER BY version DESC LIMIT 3",
                "SELECT `problems`.* FROM `problems` WHERE `problems`.`assessment_id` = 5000016",
                "SELECT `announcements`.* FROM `announcements` WHERE `announcements`.`persistent` = 1 AND (`announcements`.`course_id` = 10000000 OR `announcements`.`system` = 1)",
        };
        testQueries(queries, 27000000, 1);
    }

    @Test
    public void testProductionHomepage() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("SELECT `scheduler`.* FROM `scheduler` WHERE `scheduler`.`next` < '%1$s'"),
                new PQuery("SELECT  `users`.* FROM `users` WHERE `users`.`id` = ? ORDER BY `users`.`id` ASC LIMIT ?", 27000000, 1),
                new PQuery("SELECT  1 AS one FROM `courses` INNER JOIN `course_user_data` ON `courses`.`id` = `course_user_data`.`course_id` WHERE `course_user_data`.`user_id` = ? LIMIT ?", 27000000, 1),
                new PQuery("SELECT `courses`.`id`, `courses`.`name`, `courses`.`display_name`, `courses`.`start_date`, `courses`.`end_date`, `courses`.`disabled`, `courses`.`semester` FROM `courses` INNER JOIN `course_user_data` ON `courses`.`id` = `course_user_data`.`course_id` WHERE `course_user_data`.`user_id` = ? ORDER BY display_name ASC", 27000000),
                new PQuery("SELECT  `users`.* FROM `users` WHERE `users`.`id` = ? LIMIT ?", 27000000, 1),
                new PQuery("SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = ? AND `course_user_data`.`course_id` = ? LIMIT ?", 27000000, 10000000, 1),
                new PQuery("SELECT  `users`.`id`, `users`.`first_name`, `users`.`last_name`, `users`.`email`, `users`.`school`, `users`.`major`, `users`.`year`, `users`.`administrator` FROM `users` WHERE `users`.`id` = ? LIMIT ?", 27000000, 1),
                new PQuery("SELECT `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = ? AND (start_at < '%1$s' AND end_at > '%1$s') ORDER BY due_at ASC, name ASC", 10000000),
                new PQuery("SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = ? AND `course_user_data`.`course_id` = ? LIMIT 1", 27000000, 10000001),
                new PQuery("SELECT `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = ? AND (start_at < '%1$s' AND end_at > '%1$s') ORDER BY due_at ASC, name ASC", 10000001),
                new PQuery("SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = ? AND `course_user_data`.`course_id` = ? LIMIT ?", 27000000, 10000002, 1),
                new PQuery("SELECT `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = ? AND (start_at < '%1$s' AND end_at > '%1$s') ORDER BY due_at ASC, name ASC", 10000002),
        };
        testQueries(queries, 27000000, 100000);
    }

    @Test
    public void testProductionShowGradebook() throws ClassNotFoundException, SQLException {
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
        };
        testQueries(queries, 27000050, 1);
    }
    @Test
    public void testProductionDownload() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("SELECT `scheduler`.* FROM `scheduler` WHERE `scheduler`.`next` < '%1$s'"),
                new PQuery("SELECT  `users`.* FROM `users` WHERE `users`.`id` = ? ORDER BY `users`.`id` ASC LIMIT ?", 27000000, 1),
                new PQuery("SELECT `courses`.`id`, `courses`.`name` FROM `courses` WHERE `courses`.`name` = ? LIMIT ?", "Course0", 1),
                new PQuery("SELECT  `course_user_data`.* FROM `course_user_data` WHERE `course_user_data`.`user_id` = ? AND `course_user_data`.`course_id` = ? LIMIT ?", 27000000, 10000000, 1),
                new PQuery("SELECT `courses`.* FROM `courses` WHERE `courses`.`id` = ? AND `courses`.`disabled` = ? LIMIT ?", 10000000, false, 1),
                new PQuery("SELECT  `users`.`id`, `users`.`first_name`, `users`.`last_name`, `users`.`email`, `users`.`school`, `users`.`major`, `users`.`year`, `users`.`administrator` FROM `users` WHERE `users`.`id` = ? LIMIT ?", 27000000, 1),
                new PQuery("SELECT  `assessments`.`id`, `assessments`.`due_at`, `assessments`.`end_at`, `assessments`.`start_at`, `assessments`.`name`, `assessments`.`updated_at`, `assessments`.`course_id`, `assessments`.`display_name`, `assessments`.`max_grace_days`, `assessments`.`category_name` FROM `assessments` WHERE `assessments`.`course_id` = ? AND `assessments`.`name` = ? LIMIT ?", 10000000, "quiz4", 1),
                new PQuery("SELECT  1 AS one FROM `submissions` WHERE `submissions`.`assessment_id` = ? AND `submissions`.`id` = ? LIMIT ?", 5000016, 26000028, 1),
                new PQuery("SELECT  `submissions`.`id`, `submissions`.`version`, `submissions`.`course_user_datum_id`, `submissions`.`assessment_id`, `submissions`.`filename`, `submissions`.`created_at`, `submissions`.`updated_at`, `submissions`.`notes`, `submissions`.`mime_type`, `submissions`.`special_type`, `submissions`.`submitted_by_id`, `submissions`.`autoresult`, `submissions`.`detected_mime_type`, `submissions`.`submitter_ip`, `submissions`.`tweak_id`, `submissions`.`ignored`, `submissions`.`dave`, `submissions`.`settings`, `submissions`.`embedded_quiz_form_answer`, `submissions`.`submitted_by_app_id` FROM `submissions` WHERE `submissions`.`assessment_id` = ? AND `submissions`.`id` = ? AND `submissions`.`course_user_datum_id` = ? LIMIT ?", 5000016, 26000028, 9000000, 1),
                new PQuery("SELECT  `assessments`.* FROM `assessments` WHERE `assessments`.`id` = ? LIMIT ?", 5000016, 1),
                new PQuery("SELECT  `submissions`.* FROM `submissions` WHERE `submissions`.`id` = ? LIMIT ?", 26000028, 1),
        };
        testQueries(queries, 27000000, 1);
    }

    @Test
    public void testFetchSchema() throws SQLException, SqlParseException, ValidationException {
        Properties info = new Properties();
        info.put("model",
                "inline:"
                        + "{\n"
                        + "  version: '1.0',\n"
                        + "  defaultSchema: 'MAIN',\n"
                        + "  schemas: [\n"
                        + "     {\n"
                        + "       type: 'jdbc',\n"
                        + "       name: 'MAIN',\n"
                        + "       jdbcDriver: 'com.mysql.jdbc.Driver',\n"
                        + "       jdbcUrl: '" + dbUrl + "',\n"
                        + "       jdbcUser: '" + dbUsername + "',\n"
                        + "       jdbcPassword: '" + dbPassword + "',\n"
                        + "       jdbcCatalog: null,\n"
                        + "       jdbcSchema: null\n"
                        + "     }\n"
                        + "  ]\n"
                        + "}");
        try (Connection conn = DriverManager.getConnection("jdbc:calcite:", info)) {
            CalciteConnection calciteConn = conn.unwrap(CalciteConnection.class);
//            SqlParserImplFactory factory = calciteConn.config().parserFactory(SqlParserImplFactory.class, null);
//            SqlParser parser = SqlParser.create("SELECT * FROM users",
//                    SqlParser.config().withParserFactory(calciteConn.config().parserFactory(SqlParserImplFactory.class, null)));
//            System.out.println(parser.parseQuery());
//            SqlAbstractParserImpl parser = factory.getParser(new SourceStringReader("SELECT * FROM users"));
//            parser.parse
            SchemaPlus rootSchema = calciteConn.getRootSchema();
            JdbcSchema dbSchema = rootSchema.getSubSchema("MAIN").unwrap(JdbcSchema.class);
//            RelDataType rdt = rootSchema.getSubSchema("MAIN").getTable("watchlist_instances").getRowType(
//                    new SqlTypeFactoryImpl(RelDataTypeSystem.DEFAULT)
//            );
//            List<RelDataTypeField> fields = rdt.getFieldList();
//            System.out.println(fields);

            SqlParser.Config parserConfig = dbSchema.dialect.configureParser(SqlParser.config()).withQuotedCasing(Casing.UNCHANGED);
//            SqlParser parser = SqlParser.create("SELECT 1 AS ONE FROM users", parserConfig);
//            System.out.println(parser.parseQuery());

            FrameworkConfig config = Frameworks.newConfigBuilder()
                    .parserConfig(parserConfig)
                    .defaultSchema(rootSchema.getSubSchema("MAIN"))
                    .build();
            Planner planner = Frameworks.getPlanner(config);
            SqlNode sqlNode = planner.parse("SELECT submissions.id AS submission_id, problems.id AS problem_id, scores.id AS score_id, scores.* FROM `submissions` JOIN problems ON" +
                    "        submissions.assessment_id = problems.assessment_id JOIN scores ON" +
                    "        (submissions.id = scores.submission_id" +
                    "        AND problems.id = scores.problem_id AND scores.released = 1) WHERE `submissions`.`assessment_id` = 4 AND `submissions`.`course_user_datum_id` = 2");
            System.out.println(sqlNode);

            Pair<SqlNode, RelDataType> p = planner.validateAndGetType(sqlNode);
            System.out.println(p.left);
            System.out.println(p.right);
        }
    }

    private record PQuery(String query, Object... params) { }
}
