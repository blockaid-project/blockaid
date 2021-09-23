package client;

import edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyConnection;
import org.flywaydb.core.Flyway;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import policy_checker.QueryChecker;
import server.EndToEndTest;
import util.Options;

import java.nio.charset.StandardCharsets;
import java.sql.*;
import java.util.ArrayList;
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
//        sql.append("INSERT INTO data_sources VALUES(1, 'H2', '").append(h2Url).append("',1,0,'CANONICAL','JDBC',NULL,NULL,NULL);\n");
//        sql.append("DROP DATABASE IF EXISTS diaspora_db;DROP DATABASE IF EXISTS diaspora_db_server;CREATE DATABASE diaspora_db;CREATE DATABASE diaspora_db_server;");
        sql.append("INSERT INTO data_sources VALUES(1, 'MySQL', '").append(h2Url).append("',1,0,'CANONICAL','JDBC',NULL,NULL,NULL);;;\n");
        sql.append("INSERT INTO jdbc_sources VALUES(1, '").append(dbUsername).append("','").append(dbPassword).append("');;;\n");
        sql.append("UPDATE ds_sets SET default_datasource_id = 1 WHERE id = 1;;;\n");
        return sql.toString();
    }

    private String readSchemaSQL() throws Exception {
//        java.net.URL url = EndToEndTest.class.getResource("/DiasporaTest/schema.sql");
        java.net.URL url = EndToEndTest.class.getResource("/DiasporaTest/dump.sql");
        java.nio.file.Path resPath = java.nio.file.Paths.get(url.toURI());
        return new String(java.nio.file.Files.readAllBytes(resPath), StandardCharsets.UTF_8);
    }

    private void setupTables(String dbUrl, String sql) throws ClassNotFoundException, SQLException {
        Class.forName("org.h2.Driver");

        Properties props = new Properties();
        props.setProperty("user", "sa");
        props.setProperty("password", "");

        Connection connection = DriverManager.getConnection(dbUrl, props);

        Statement stmt = connection.createStatement();
        for (String s : sql.split(";;;")) {
            if (s.trim().equals("")) continue;
            stmt.execute(s);
        }
    }

    @Before
    public void setupDb() throws Exception {
        java.net.URL url = EndToEndTest.class.getResource("/DiasporaTest/policies.sql");
        java.nio.file.Path resPath = java.nio.file.Paths.get(url.toURI());
        java.net.URL pk_url = EndToEndTest.class.getResource("/DiasporaTest/pk.txt");
        java.nio.file.Path pk_resPath = java.nio.file.Paths.get(pk_url.toURI());
        java.net.URL fk_url = EndToEndTest.class.getResource("/DiasporaTest/fk.txt");
        java.nio.file.Path fk_resPath = java.nio.file.Paths.get(fk_url.toURI());
        java.net.URL deps_url = EndToEndTest.class.getResource("/DiasporaTest/deps.sql");
        java.nio.file.Path deps_resPath = java.nio.file.Paths.get(deps_url.toURI());

//        String dbFile = tempFolder.newFile("Db").getPath();
//        String h2File = tempFolder.newFile("DbServer").getPath();
//        String dbUrl = "jdbc:h2:" + dbFile;
//        String h2Url = "jdbc:h2:" + h2File;
        String dbUrl = "jdbc:mysql://localhost:3306/diaspora_db?useUnicode=true&useJDBCCompliantTimezoneShift=true&useLegacyDatetimeCode=false&serverTimezone=UTC";
        String h2Url = "jdbc:mysql://localhost:3306/diaspora_db_server?useUnicode=true&useJDBCCompliantTimezoneShift=true&useLegacyDatetimeCode=false&serverTimezone=UTC";
        proxyUrl = "jdbc:privacy:thin:" + resPath + "," + deps_resPath + "," + dbUrl + "," + h2Url + "," + pk_resPath + "," + fk_resPath;

        Flyway flyway = new Flyway();
        flyway.setDataSource(dbUrl, dbUsername, dbPassword);
        flyway.migrate();

        setupTables(dbUrl, generateDBSQL(h2Url));
        setupTables(h2Url, readSchemaSQL());
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

        QueryChecker.PRECHECK_SETTING = QueryChecker.PrecheckSetting.DISABLED;
        QueryChecker.UNNAMED_EQUALITY = true;
        QueryChecker.SOLVE_TIMEOUT_MS = 10000;

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        String query = "INSERT INTO users(id, username, email, getting_started, disable_mail, `language`) VALUES (?, ?, ?, ?, ?, ?)";
//        PreparedStatement s = conn.prepareStatement(query);
//        s.setInt(1, 1);
//        s.setString(2, "aaaa");
//        s.setString(3, "foo@bar.com");
//        s.setBoolean(4, false);
//        s.setBoolean(5, false);
//        s.setString(6, "en");
//        s.execute();
//        s.setInt(1, 3);
//        s.setString(2, "bbbb");
//        s.setString(3, "bar@foo.com");
//        s.setBoolean(4, true);
//        s.setBoolean(5, false);
//        s.setString(6, "es");
//        s.execute();

        query = "SELECT id, username, email, getting_started, disable_mail, `language` FROM users WHERE users.id IN (?_MY_UID) AND users.id = ?";
        PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
        p.setInt(1, 1);
        p.setInt(2, 1);
        p.executeQuery();

        query = "SELECT username FROM users WHERE username = ? AND email = ? AND `language` = ?";
        p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
        p.setString(1, "aaaa");
        p.setString(2, "foo@bar.com");
        p.setString(3, "en");
        p.executeQuery();

        ((PrivacyConnection) conn).resetSequence();
        Thread.sleep(5000);

        query = "SELECT id, username, email, getting_started, disable_mail, `language` FROM users WHERE users.id IN (?_MY_UID) AND users.id = ?";
        p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
        p.setInt(1, 3);
        p.setInt(2, 1);
        p.executeQuery();

        query = "SELECT username FROM users WHERE username = ? AND email = ? AND `language` = ?";
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

        Options.ENABLE_CACHING = false;
        QueryChecker.PRECHECK_SETTING = QueryChecker.PrecheckSetting.DISABLED;
        QueryChecker.SOLVE_TIMEOUT_MS = 3000;

        long startTime, endTime;
        startTime = System.nanoTime();

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        endTime = System.nanoTime();
        System.err.println("setup time: " + (endTime - startTime) / 1000000.0);
        startTime = System.nanoTime();

        String query = "INSERT INTO users(id, username) VALUES (?, ?)";
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
        QueryChecker.PRECHECK_SETTING = QueryChecker.PrecheckSetting.DISABLED;
        QueryChecker.SOLVE_TIMEOUT_MS = 30000;

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

        Options.ENABLE_CACHING = true;
        QueryChecker.PRECHECK_SETTING = QueryChecker.PrecheckSetting.DISABLED;
        QueryChecker.SOLVE_TIMEOUT_MS = 15000;

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        String[] queries = new String[]{
                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = ?_MY_UID ORDER BY `users`.`id` ASC LIMIT 1",
//                "SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = 'Post' WHERE `posts`.`id` = 10 AND `share_visibilities`.`user_id` = ?_MY_UID ORDER BY `posts`.`id` ASC LIMIT 1",
                "SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = ?_MY_UID LIMIT 1",
//                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = 10 AND `posts`.`author_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
//                "SELECT `mentions`.`id` FROM `mentions` WHERE `mentions`.`mentions_container_id` = 10 AND `mentions`.`mentions_container_type` = 'Post' AND `mentions`.`person_id` = 1",
//                "SELECT `mentions`.`id` FROM `mentions` INNER JOIN `comments` ON `mentions`.`mentions_container_id` = `comments`.`id` AND `mentions`.`mentions_container_type` = 'Comment' WHERE `comments`.`commentable_id` = 10 AND `comments`.`commentable_type` = 'Post'",
//                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 10 AND `mentions`.`mentions_container_type` = 'Post'",
//                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 2",
//                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 2",
//                "SELECT  `people`.* FROM `people` WHERE `people`.`id` = 1 LIMIT 1",
//                "SELECT  `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 1 LIMIT 1",
//                "SELECT `photos`.* FROM `photos` WHERE `photos`.`status_message_guid` = '78ff2810603c01392a5d0665b8726074'",
//                "SELECT  `locations`.* FROM `locations` WHERE `locations`.`status_message_id` = 10 LIMIT 1",
//                "SELECT  `polls`.* FROM `polls` WHERE `polls`.`status_message_id` = 10 LIMIT 1",
//                "SELECT  1 AS one_ FROM `participations` WHERE `participations`.`author_id` = 1 AND `participations`.`target_id` = 10 LIMIT 1",
//                "SELECT  `likes`.* FROM `likes` WHERE `likes`.`target_id` = 10 AND `likes`.`target_type` = 'Post' AND `likes`.`positive` = TRUE AND `likes`.`author_id` = 1 LIMIT 1",
//                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`type` IN ('Reshare') AND `posts`.`root_guid` = '78ff2810603c01392a5d0665b8726074' AND `posts`.`author_id` = 1 LIMIT 1",
//                "SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = 'Post' WHERE `posts`.`id` = 10 AND `share_visibilities`.`user_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
//                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = 10 AND `posts`.`author_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
//                "SELECT  `likes`.* FROM `likes` WHERE `likes`.`target_id` = 10 AND `likes`.`target_type` = 'Post' AND `likes`.`positive` = TRUE ORDER BY author_id = 1 DESC LIMIT 30",
//                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`type` IN ('Reshare') AND `posts`.`root_guid` = '78ff2810603c01392a5d0665b8726074' ORDER BY author_id = 1 DESC LIMIT 30",
//                "SELECT `tags`.* FROM `tags` INNER JOIN `taggings` ON `tags`.`id` = `taggings`.`tag_id` WHERE `taggings`.`taggable_id` = 10 AND `taggings`.`taggable_type` = 'Post' AND `taggings`.`context` = 'tags'",
//                "SELECT COUNT(*) FROM `notifications` WHERE `notifications`.`recipient_id` = 1 AND `notifications`.`unread` = TRUE",
//                "SELECT SUM(`conversation_visibilities`.`unread`) FROM `conversation_visibilities` WHERE `conversation_visibilities`.`person_id` = 1",
//                "SELECT  1 AS one_ FROM `roles` WHERE `roles`.`person_id` = 1 AND `roles`.`name` = 'admin' LIMIT 1",
//                "SELECT  1 AS one_ FROM `roles` WHERE `roles`.`name` IN ('moderator', 'admin') AND `roles`.`person_id` = 1 LIMIT 1",
//                "SELECT `aspects`.* FROM `aspects` WHERE `aspects`.`user_id` = 1 ORDER BY order_id ASC",
//                "SELECT `services`.* FROM `services` WHERE `services`.`user_id` = 1",
//                "SELECT COUNT(*) FROM `contacts` WHERE `contacts`.`user_id` = 1 AND `contacts`.`receiving` = TRUE",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 1 ORDER BY `users`.`id` ASC LIMIT 1",
//                "SELECT COUNT(*) FROM `notifications` WHERE `notifications`.`recipient_id` = 1",
//                "SELECT  `notifications`.* FROM `notifications` WHERE `notifications`.`recipient_id` = 1 ORDER BY updated_at desc LIMIT 10 OFFSET 0",
//                "SELECT `posts`.* FROM `posts` WHERE `posts`.`id` IN (10, 7, 1)",
//                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`id` = 2",
//                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 2",
//                //"SELECT `notification_actors`.* FROM `notification_actors` WHERE `notification_actors`.`notification_id` IN (11, 10, 8, 7, 3, 2, 1)",
//                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 2",
//                "SELECT COUNT(*) FROM `notifications` WHERE `notifications`.`recipient_id` = 1 AND `notifications`.`unread` = TRUE",
//                "SELECT `notifications`.* FROM `notifications` WHERE `notifications`.`recipient_id` = 1 AND `notifications`.`unread` = TRUE",
//                "SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = 1 LIMIT 1",
//                "SELECT  `people`.* FROM `people` WHERE `people`.`id` = 1 LIMIT 1",
//                "SELECT  `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 1 LIMIT 1",
//                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 10 AND `mentions`.`mentions_container_type` = 'Post'",
//                "SELECT  `comments`.* FROM `comments` WHERE `comments`.`id` = 3 LIMIT 1",
//                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = 10 LIMIT 1",
//                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 7 AND `mentions`.`mentions_container_type` = 'Post'",
//                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 1 AND `mentions`.`mentions_container_type` = 'Post'",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 1 ORDER BY `users`.`id` ASC LIMIT 1",
//                "SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = 'Post' WHERE `posts`.`id` = 10 AND `share_visibilities`.`user_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
//                "SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = 1 LIMIT 1",
//                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = 10 AND `posts`.`author_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
//                "SELECT `comments`.* FROM `comments` WHERE `comments`.`commentable_id` = 10 AND `comments`.`commentable_type` = 'Post' ORDER BY created_at ASC",
//                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 2",
//                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 2",
//                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 3 AND `mentions`.`mentions_container_type` = 'Comment'",
//                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 1",
//                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 1",
//                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 4 AND `mentions`.`mentions_container_type` = 'Comment'",
//                "SELECT  `users`.* FROM `users` WHERE `users`.`id` = 1 ORDER BY `users`.`id` ASC LIMIT 1",
//                "SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = 'Post' WHERE `posts`.`id` = 10 AND `share_visibilities`.`user_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
//                "SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = 1 LIMIT 1",
//                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = 10 AND `posts`.`author_id` = 1 ORDER BY `posts`.`id` ASC LIMIT 1",
//                "SELECT `comments`.* FROM `comments` WHERE `comments`.`commentable_id` = 10 AND `comments`.`commentable_type` = 'Post' ORDER BY created_at ASC",
//                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 2",
//                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 2",
//                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 3 AND `mentions`.`mentions_container_type` = 'Comment'",
//                "SELECT `people`.* FROM `people` WHERE `people`.`id` = 1",
//                "SELECT `profiles`.* FROM `profiles` WHERE `profiles`.`person_id` = 1",
//                "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = 4 AND `mentions`.`mentions_container_type` = 'Comment'",
//
//                // mentions_container_id, mentions_container_type not fully specified
////                "SELECT `mentions`.`id` FROM `mentions` INNER JOIN comments ON mentions_container_id = comments.id AND mentions_container_type = 'Comment' WHERE `comments`.`commentable_id` = 23 AND `comments`.`commentable_type` = 'Post'",
//                // unread not fully specified
////                "SELECT  `conversation_visibilities`.* FROM `conversation_visibilities` WHERE `conversation_visibilities`.`conversation_id` = 1 AND `conversation_visibilities`.`person_id` = 2 AND (unread > 0) ORDER BY `conversation_visibilities`.`id` ASC LIMIT 1",
//                // subquery
////                "SELECT COUNT(*) FROM (SELECT DISTINCT `conversation_visibilities`.`id` FROM `conversation_visibilities` INNER JOIN `conversations` ON `conversations`.`id` = `conversation_visibilities`.`conversation_id` WHERE `conversation_visibilities`.`person_id` = 2) subquery_for_count",
////                "SELECT COUNT(*) FROM (SELECT DISTINCT photos.* FROM `photos` LEFT OUTER JOIN share_visibilities ON share_visibilities.shareable_id = photos.id AND share_visibilities.shareable_type = 'Photo' WHERE `photos`.`author_id` = 3 AND (`share_visibilities`.`user_id` = 2 OR `photos`.`public` = TRUE) AND (photos.created_at < '2021-04-20 19:58:20.330912') AND `photos`.`pending` = FALSE ORDER BY photos.created_at DESC, created_at DESC) subquery_for_count",
//                // outer join
////                "SELECT  `conversation_visibilities`.`id` AS t0_r0, `conversation_visibilities`.`conversation_id` AS t0_r1, `conversation_visibilities`.`person_id` AS t0_r2, `conversation_visibilities`.`unread` AS t0_r3, `conversation_visibilities`.`created_at` AS t0_r4, `conversation_visibilities`.`updated_at` AS t0_r5, `conversations`.`id` AS t1_r0, `conversations`.`subject` AS t1_r1, `conversations`.`guid` AS t1_r2, `conversations`.`author_id` AS t1_r3, `conversations`.`created_at` AS t1_r4, `conversations`.`updated_at` AS t1_r5 FROM `conversation_visibilities` LEFT OUTER JOIN `conversations` ON `conversations`.`id` = `conversation_visibilities`.`conversation_id` WHERE `conversation_visibilities`.`person_id` = 2 ORDER BY conversations.updated_at DESC LIMIT 15 OFFSET 0",
////                "SELECT  DISTINCT posts.* FROM `posts` LEFT OUTER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE `posts`.`author_id` = 3 AND (`share_visibilities`.`user_id` = 2 OR `posts`.`public` = TRUE) AND (posts.created_at < '2021-04-20 19:58:33') AND `posts`.`type` IN ('StatusMessage', 'Reshare') AND (posts.id NOT IN ('22')) ORDER BY posts.created_at desc, posts.created_at DESC, posts.id DESC LIMIT 15",
////                "(SELECT DISTINCT posts.id, posts.updated_at AS updated_at, posts.created_at AS created_at FROM `posts` LEFT OUTER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE `posts`.`author_id` = 3 AND (`share_visibilities`.`user_id` = 2 AND `share_visibilities`.`shareable_type` = 'Post' AND `share_visibilities`.`hidden` = FALSE OR `posts`.`public` = TRUE) AND `posts`.`type` IN ('StatusMessage', 'Reshare') AND `posts`.`created_at` < '2021-03-27 01:30:44' ORDER BY posts.created_at DESC LIMIT 15) UNION ALL (SELECT DISTINCT posts.id, posts.updated_at AS updated_at, posts.created_at AS created_at FROM `posts` WHERE `posts`.`author_id` = 2 AND `posts`.`type` IN ('StatusMessage', 'Reshare') AND `posts`.`created_at` < '2021-03-27 01:30:44' ORDER BY posts.created_at DESC LIMIT 15) ORDER BY created_at DESC LIMIT 15",
////                "SELECT  DISTINCT posts.*, posts.id FROM `posts` INNER JOIN `mentions` ON `mentions`.`mentions_container_id` = `posts`.`id` AND `mentions`.`mentions_container_type` = 'Post' LEFT OUTER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE `posts`.`type` IN ('StatusMessage') AND (`share_visibilities`.`user_id` = 2 OR (`posts`.`public` = TRUE OR `posts`.`author_id` = 2)) AND `mentions`.`person_id` = 2 AND (posts.created_at < '2021-03-27 01:30:44') AND `posts`.`type` IN ('StatusMessage', 'Reshare') ORDER BY posts.created_at DESC, posts.id DESC LIMIT 15",
//                // date comparison
//                "SELECT  DISTINCT posts.*, posts.id FROM `posts` INNER JOIN `taggings` ON `taggings`.`taggable_id` = `posts`.`id` AND `taggings`.`taggable_type` = 'Post' WHERE `posts`.`type` IN ('StatusMessage') AND `posts`.`public` = TRUE AND (taggings.tag_id IN (2,4)) AND (posts.author_id NOT IN (1)) AND (posts.created_at < '2021-03-27 01:30:44') AND `posts`.`type` IN ('StatusMessage', 'Reshare') ORDER BY posts.created_at DESC, posts.id DESC LIMIT 15",
//                "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` IN (21, 20, 18, 17, 16, 15, 14, 13, 12, 8, 2, 14, 2, 10) AND (posts.created_at < '2021-03-27 01:30:44') AND `posts`.`type` IN ('StatusMessage', 'Reshare') AND (posts.author_id NOT IN (1)) ORDER BY posts.created_at DESC, posts.id DESC LIMIT 15",
        };

        for (String query : queries) {
            System.err.println(query);
            System.err.println(System.nanoTime());
            PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
            System.err.println(p.checkPolicy());
            System.err.println(System.nanoTime());
        }
    }

    @Test
    public void runTrace() throws Exception {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
        Class.forName("com.mysql.jdbc.Driver");

        QueryChecker.PRECHECK_SETTING = QueryChecker.PrecheckSetting.DISABLED;
        QueryChecker.UNNAMED_EQUALITY = true;
        QueryChecker.SOLVE_TIMEOUT_MS = 10000;

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        Statement statement = conn.createStatement();
        statement.execute("SET @_MY_UID=2");

        String query = "SELECT  `users`.* FROM `users` WHERE `users`.`id` = ? ORDER BY `users`.`id` ASC LIMIT 1";
        System.err.println(query);
        PreparedStatement p = conn.prepareStatement(query);
        p.setInt(1, 2);
        p.executeQuery();

        query = "SELECT  `users`.* FROM `users` WHERE `users`.`id` = ? ORDER BY `users`.`id` ASC LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 2);
        p.executeQuery();

        query = "SELECT  `users`.* FROM `users` WHERE `users`.`id` = ? ORDER BY `users`.`id` ASC LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 2);
        p.executeQuery();

        query = "SELECT  `users`.* FROM `users` WHERE `users`.`invited_by_id` = ? ORDER BY `users`.`id` ASC LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 3);
        p.executeQuery();

        query = "SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = ? WHERE `posts`.`id` = ? AND `share_visibilities`.`user_id` = ?_MY_UID ORDER BY `posts`.`id` ASC LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setString(1, "Post");
        p.setInt(2, 4);
        p.setInt(3, 2);
        p.executeQuery();

        query = "SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = ?_MY_UID LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 2);
        p.executeQuery();

        query = "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = ? AND `posts`.`author_id` = ? ORDER BY `posts`.`id` ASC LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 4);
        p.setInt(2, 3);
        p.executeQuery();

        query = "UPDATE `notifications` SET `unread` = 0 WHERE `recipient_id` = ? AND `target_type` = ? AND `target_id` = ? AND `unread` = ?";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 2);
        p.setString(2, "Post");
        p.setInt(3, 4);
        p.setInt(4, 1);
        p.execute();

        query = "SELECT `mentions`.`id` FROM `mentions` WHERE `mentions`.`mentions_container_id` = ? AND `mentions`.`mentions_container_type` = ? AND `mentions`.`person_id` = ?";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 4);
        p.setString(2, "Post");
        p.setInt(3, 3);
        p.executeQuery();

        query = "SELECT `mentions`.`id` FROM `mentions` INNER JOIN comments ON mentions.mentions_container_id = comments.id AND mentions.mentions_container_type = ? WHERE `comments`.`commentable_id` = ? AND `comments`.`commentable_type` = ?";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setString(1, "Comment");
        p.setInt(2, 4);
        p.setString(3, "Post");
        p.executeQuery();

        query = "SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = ? AND `mentions`.`mentions_container_type` = ?";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 4);
        p.setString(2, "Post");
        p.executeQuery();

        query = "SELECT  `people`.* FROM `people` WHERE `people`.`id` = ? LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 3);
        p.executeQuery();

        query = "SELECT  profiles.id, profiles.diaspora_handle, profiles.first_name, profiles.last_name, profiles.image_url, profiles.image_url_small, profiles.image_url_medium, profiles.searchable, profiles.person_id, profiles.created_at, profiles.updated_at, profiles.full_name, profiles.nsfw, profiles.public_details FROM `profiles` WHERE `profiles`.`person_id` = ? LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 3);
        p.executeQuery();

        query = "SELECT `photos`.* FROM `photos` WHERE `photos`.`status_message_guid` = ?";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setString(1, "46d948707ae60139ec3e5db4b3e77b69");
        p.executeQuery();

        query = "SELECT  `locations`.* FROM `locations` WHERE `locations`.`status_message_id` = ? LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 4);
        p.executeQuery();

        query = "SELECT  `polls`.* FROM `polls` WHERE `polls`.`status_message_id` = ? LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 4);
        p.executeQuery();

        query = "SELECT  1 AS one_ FROM `participations` WHERE `participations`.`author_id` = ? AND `participations`.`target_id` = ? LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 3);
        p.setInt(2, 4);
        p.executeQuery();

        query = "SELECT  `likes`.* FROM `likes` WHERE `likes`.`target_id` = ? AND `likes`.`target_type` = ? AND `likes`.`positive` = ? AND `likes`.`author_id` = ? LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 4);
        p.setString(2, "Post");
        p.setInt(3, 1);
        p.setInt(4, 3);
        p.executeQuery();

        query = "SELECT  `posts`.* FROM `posts` WHERE `posts`.`type` IN (?) AND `posts`.`root_guid` = ? AND `posts`.`author_id` = ? LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setString(1, "Reshare");
        p.setString(2, "46d948707ae60139ec3e5db4b3e77b69");
        p.setInt(3, 3);
        p.executeQuery();

        query = "SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = ? WHERE `posts`.`id` = ? AND `share_visibilities`.`user_id` = ?_MY_UID ORDER BY `posts`.`id` ASC LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setString(1, "Post");
        p.setInt(2, 4);
        p.setInt(3, 2);
        p.executeQuery();

        query = "SELECT  `posts`.* FROM `posts` WHERE `posts`.`id` = ? AND `posts`.`author_id` = ? ORDER BY `posts`.`id` ASC LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 4);
        p.setInt(2, 3);
        p.executeQuery();

        query = "SELECT  `likes`.* FROM `likes` WHERE `likes`.`target_id` = ? AND `likes`.`target_type` = ? AND `likes`.`positive` = ? ORDER BY author_id = 3 DESC LIMIT 30";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 4);
        p.setString(2, "Post");
        p.setInt(3, 1);
        p.executeQuery();

        query = "SELECT  `posts`.* FROM `posts` WHERE `posts`.`type` IN (?) AND `posts`.`root_guid` = ? ORDER BY author_id = 3 DESC LIMIT 30";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setString(1, "Reshare");
        p.setString(2, "46d948707ae60139ec3e5db4b3e77b69");
        p.executeQuery();

        query = "SELECT `tags`.* FROM `tags` INNER JOIN `taggings` ON `tags`.`id` = `taggings`.`tag_id` WHERE `taggings`.`taggable_id` = ? AND `taggings`.`taggable_type` = ? AND `taggings`.`context` = ?";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 4);
        p.setString(2, "Post");
        p.setString(3, "tags");
        p.executeQuery();

        query = "SELECT COUNT(*) FROM `notifications` WHERE `notifications`.`recipient_id` = ?_MY_UID AND `notifications`.`unread` = ?";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 2);
        p.setInt(2, 1);
        p.executeQuery();

        query = "SELECT SUM(`conversation_visibilities`.`unread`) FROM `conversation_visibilities` WHERE `conversation_visibilities`.`person_id` = ?";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 3);
        p.executeQuery();

        query = "SELECT  1 AS one_ FROM `roles` WHERE `roles`.`person_id` = ? AND `roles`.`name` = ? LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 3);
        p.setString(2, "admin");
        p.executeQuery();

        query = "SELECT  1 AS one_ FROM `roles` WHERE `roles`.`name` IN (?, ?) AND `roles`.`person_id` = ? LIMIT 1";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setString(1, "moderator");
        p.setString(2, "admin");
        p.setInt(3, 3);
        p.executeQuery();

        query = "SELECT `aspects`.* FROM `aspects` WHERE `aspects`.`user_id` = ?_MY_UID ORDER BY order_id ASC";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 2);
        p.executeQuery();

        query = "SELECT `services`.* FROM `services` WHERE `services`.`user_id` = ?_MY_UID";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 2);
        p.executeQuery();

        query = "SELECT COUNT(*) FROM `contacts` WHERE `contacts`.`user_id` = ?_MY_UID AND `contacts`.`receiving` = ?";
        System.err.println(query);
        p = conn.prepareStatement(query);
        p.setInt(1, 2);
        p.setInt(2, 1);
        p.executeQuery();

        ((PrivacyConnection) conn).resetSequence();
        Thread.sleep(5000);
    }
}
