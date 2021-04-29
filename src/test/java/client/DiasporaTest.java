package client;

import edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyConnection;
import org.flywaydb.core.Flyway;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import policy_checker.QueryChecker;
import server.EndToEndTest;

import java.nio.charset.StandardCharsets;
import java.sql.*;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
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
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
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
    public void runTestSetConst() throws Exception {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        try (PrivacyConnection conn =
                     (PrivacyConnection) DriverManager.getConnection(proxyUrl, dbUsername, dbPassword)) {
            conn.setAutoCommit(true);

            // todo: data needs to be generated or we're querying an empty database

            for (int i = 0; i < 3; i++) {
                try (Statement stmt = conn.createStatement()) {
                    stmt.execute("SET @_MY_UID = 2");
                }

                String query = "SELECT username FROM users WHERE id = 2";
                try (PrivacyConnection.PrivacyPreparedStatement p =
                             (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query)) {
                    assertTrue(p.checkPolicy());
                }
                conn.resetSequence();
            }
        }
    }

    @Test
    public void runSimpleTestWithData() throws Exception {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        QueryChecker.ENABLE_PRECHECK = false;
        QueryChecker.SOLVE_TIMEOUT = 10000;

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        String query = "INSERT INTO users(id, username, email, getting_started, disable_mail, `language`) VALUES (??, ??, ??, ??, ??, ??)";
        PreparedStatement s = conn.prepareStatement(query);
        s.setInt(1, 1);
        s.setString(2, "aaaa");
        s.setString(3, "foo@bar.com");
        s.setBoolean(4, false);
        s.setBoolean(5, false);
        s.setString(6, "en");
        s.execute();

        query = "SELECT id, username, email, getting_started, disable_mail, `language` FROM users WHERE users.id IN (?_MY_UID) AND users.id = ??";
        PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
        p.setInt(1, 1);
        p.setInt(2, 1);
        p.executeQuery();

        query = "SELECT username FROM users WHERE username = ?? AND email = ?? AND `language` = ??";
        p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
        p.setString(1, "aaaa");
        p.setString(2, "foo@bar.com");
        p.setString(3, "en");
        p.executeQuery();

        Thread.sleep(5000);
    }

    @Test
    public void testViewMyPost() throws Exception {
        Class.forName("jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        QueryChecker.ENABLE_CACHING = false;
        QueryChecker.ENABLE_PRECHECK = true;

        long startTime, endTime;
        startTime = System.nanoTime();

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        endTime = System.nanoTime();
        System.err.println("setup time: " + (endTime - startTime) / 1000000.0);
        startTime = System.nanoTime();

        String query = "INSERT INTO users(id, username) VALUES (??, ??)";
        PreparedStatement s = conn.prepareStatement(query);
        s.setInt(1, 1);
        s.setString(2, "aaaa");
        s.execute();

        endTime = System.nanoTime();
        System.err.println("data entry time: " + (endTime - startTime) / 1000000.0);

        List<Long> times = new ArrayList<>();
        for (int i = 0; i < 1000; ++i) {
            startTime = System.nanoTime();

            query = "SELECT users.id FROM users WHERE users.id = ?_MY_UID ORDER BY users.id ASC LIMIT 1";
            PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
            p.setInt(1, 1);

            endTime = System.nanoTime();
            System.err.println("query prepare time: " + (endTime - startTime) / 1000000.0);
            startTime = System.nanoTime();

            p.executeQuery();

            endTime = System.nanoTime();
            System.err.println("query run time: " + (endTime - startTime) / 1000000.0);
            times.add(endTime - startTime);

            ((PrivacyConnection) conn).resetSequence();
        }

        long y = 0;
        for (Long x : times) {
            y += x;
        }
        System.err.println("average query run time: " + (((float) y) / times.size()) / 1000000.0);
    }

    @Test
    public void runMultipleThread() throws Exception {
        QueryChecker.ENABLE_PRECHECK = false;
        QueryChecker.SOLVE_TIMEOUT = 30000;

        Thread a = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    Class.forName("jdbc.PrivacyDriver");
                    Class.forName("org.h2.Driver");

                    Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
                    conn.setAutoCommit(true);

                    String query = "SELECT username FROM users WHERE id = ?_MY_UID";
                    PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
                    p.setInt(1, 1);
                    assertTrue(p.checkPolicy());
                } catch (Throwable e) {
                    throw new RuntimeException(e);
                }
            }
        });

        Thread b = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    Class.forName("jdbc.PrivacyDriver");
                    Class.forName("org.h2.Driver");

                    Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
                    conn.setAutoCommit(true);

                    String query = "SELECT username FROM users WHERE id <> ?_MY_UID";
                    PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
                    p.setInt(1, 1);
                    assertTrue(p.checkPolicy());
                } catch (Throwable e) {
                    throw new RuntimeException(e);
                }
            }
        });

        a.start();
        b.start();
        a.join();
        b.join();
    }

    @Test
    public void testDiasporaTraceQueries() throws Exception {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        QueryChecker.ENABLE_CACHING = true;
        QueryChecker.ENABLE_PRECHECK = true;
        QueryChecker.SOLVE_TIMEOUT = 100;

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        String[] queries = new String[]{
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 1 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = 'Post' WHERE `posts`.`id` = 10 AND `share_visibilities`.`user_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
                "SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = 1 LIMIT 1",
                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = 10 AND `posts`.`author_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
                "SELECT `mentions`.`id` FROM `mentions` WHERE `mentions`.`mentions_container_id` = 10 AND `mentions`.`mentions_container_type` = 'Post' AND `mentions`.`person_id` = 1",
                "SELECT `mentions`.`id` FROM `mentions` INNER JOIN `comments` ON `mentions`.`mentions_container_id` = `comments`.`id` AND `mentions`.`mentions_container_type` = 'Comment' WHERE `comments`.`commentable_id` = 10 AND `comments`.`commentable_type` = 'Post'",
                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 10 AND `mentions`.`mentions_container_type` = 'Post'",
                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 2",
                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 2",
                "SELECT  `people`.* FROM `people` WHERE `people`.`id` = 1 LIMIT 1",
                "SELECT  `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 1 LIMIT 1",
                "SELECT `photos`.* FROM `photos` WHERE `photos`.`status_message_guid` = '78ff2810603c01392a5d0665b8726074'",
                "SELECT  `locations`.* FROM `locations` WHERE `locations`.`status_message_id` = 10 LIMIT 1",
                "SELECT  `polls`.* FROM `polls` WHERE `polls`.`status_message_id` = 10 LIMIT 1",
                "SELECT  1 AS one_ FROM `participations` WHERE `participations`.`author_id` = 1 AND `participations`.`target_id` = 10 LIMIT 1",
                "SELECT  `likes`.* FROM `likes` WHERE `likes`.`target_id` = 10 AND `likes`.`target_type` = 'Post' AND `likes`.`positive` = TRUE AND `likes`.`author_id` = 1 LIMIT 1",
                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`type` IN ('Reshare') AND `posts`.`root_guid` = '78ff2810603c01392a5d0665b8726074' AND `posts`.`author_id` = 1 LIMIT 1",
                "SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = 'Post' WHERE `posts`.`id` = 10 AND `share_visibilities`.`user_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = 10 AND `posts`.`author_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
                "SELECT  `likes`.* FROM `likes` WHERE `likes`.`target_id` = 10 AND `likes`.`target_type` = 'Post' AND `likes`.`positive` = TRUE ORDER BY author_id = 1 DESC LIMIT 30",
                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`type` IN ('Reshare') AND `posts`.`root_guid` = '78ff2810603c01392a5d0665b8726074' ORDER BY author_id = 1 DESC LIMIT 30",
                "SELECT `tags`.* FROM `tags` INNER JOIN `taggings` ON `tags`.`id` = `taggings`.`tag_id` WHERE `taggings`.`taggable_id` = 10 AND `taggings`.`taggable_type` = 'Post' AND `taggings`.`context` = 'tags'",
                "SELECT COUNT(*) FROM `notifications` WHERE `notifications`.`recipient_id` = 1 AND `notifications`.`unread` = TRUE",
                "SELECT SUM(`conversation_visibilities`.`unread`) FROM `conversation_visibilities` WHERE `conversation_visibilities`.`person_id` = 1",
                "SELECT  1 AS one_ FROM `roles` WHERE `roles`.`person_id` = 1 AND `roles`.`name` = 'admin' LIMIT 1",
                "SELECT  1 AS one_ FROM `roles` WHERE `roles`.`name` IN ('moderator', 'admin') AND `roles`.`person_id` = 1 LIMIT 1",
                "SELECT `aspects`.* FROM `aspects` WHERE `aspects`.`user_id` = 1 ORDER BY order_id ASC",
                "SELECT `services`.* FROM `services` WHERE `services`.`user_id` = 1",
                "SELECT COUNT(*) FROM `contacts` WHERE `contacts`.`user_id` = 1 AND `contacts`.`receiving` = TRUE",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 1 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT COUNT(*) FROM `notifications` WHERE `notifications`.`recipient_id` = 1",
                "SELECT  `notifications`.* FROM `notifications` WHERE `notifications`.`recipient_id` = 1 ORDER BY updated_at desc LIMIT 10 OFFSET 0",
                "SELECT `posts`.* FROM `posts` WHERE `posts`.`id` IN (10, 7, 1)",
                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`id` = 2",
                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 2",
                //"SELECT `notification_actors`.* FROM `notification_actors` WHERE `notification_actors`.`notification_id` IN (11, 10, 8, 7, 3, 2, 1)",
                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 2",
                "SELECT COUNT(*) FROM `notifications` WHERE `notifications`.`recipient_id` = 1 AND `notifications`.`unread` = TRUE",
                "SELECT `notifications`.* FROM `notifications` WHERE `notifications`.`recipient_id` = 1 AND `notifications`.`unread` = TRUE",
                "SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = 1 LIMIT 1",
                "SELECT  `people`.* FROM `people` WHERE `people`.`id` = 1 LIMIT 1",
                "SELECT  `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 1 LIMIT 1",
                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 10 AND `mentions`.`mentions_container_type` = 'Post'",
                "SELECT  `comments`.* FROM `comments` WHERE `comments`.`id` = 3 LIMIT 1",
                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = 10 LIMIT 1",
                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 7 AND `mentions`.`mentions_container_type` = 'Post'",
                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 1 AND `mentions`.`mentions_container_type` = 'Post'",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 1 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = 'Post' WHERE `posts`.`id` = 10 AND `share_visibilities`.`user_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
                "SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = 1 LIMIT 1",
                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = 10 AND `posts`.`author_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
                "SELECT `comments`.* FROM `comments` WHERE `comments`.`commentable_id` = 10 AND `comments`.`commentable_type` = 'Post' ORDER BY created_at ASC",
                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 2",
                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 2",
                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 3 AND `mentions`.`mentions_container_type` = 'Comment'",
                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 1",
                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 1",
                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 4 AND `mentions`.`mentions_container_type` = 'Comment'",
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 1 ORDER BY `users`.`id` ASC LIMIT 1",
                "SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = 'Post' WHERE `posts`.`id` = 10 AND `share_visibilities`.`user_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
                "SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = 1 LIMIT 1",
                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = 10 AND `posts`.`author_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
                "SELECT `comments`.* FROM `comments` WHERE `comments`.`commentable_id` = 10 AND `comments`.`commentable_type` = 'Post' ORDER BY created_at ASC",
                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 2",
                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 2",
                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 3 AND `mentions`.`mentions_container_type` = 'Comment'",
                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 1",
                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 1",
                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 4 AND `mentions`.`mentions_container_type` = 'Comment'",
        };

        for (String query : queries) {
            System.err.println(query);
            PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
            p.execute();
        }
    }
}
