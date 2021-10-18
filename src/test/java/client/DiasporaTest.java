package client;

import edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyConnection;
import org.apache.calcite.adapter.jdbc.JdbcSchema;
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

import java.sql.*;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.Arrays;
import java.util.Properties;

import static com.google.common.base.Preconditions.checkArgument;

public class DiasporaTest {
    private static final String dbDatabaseName = "diaspora_production_new";
    private static final String dbUrl = "jdbc:mysql://127.0.0.1:3306/" + dbDatabaseName +
            "?useSSL=false&useUnicode=true&character_set_server=utf8mb4&collation_server=utf8mb4_bin";
    private static final String dbUsername = "diaspora";
    private static final String dbPassword = "12345678";
    private static final String resourcePath = "/home/ubuntu/diaspora/policy";

    private String proxyUrl;

    @Before
    public void setupDb() {
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
    public void testSimplePost() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("SELECT  `users`.* FROM `users` WHERE `users`.`id` = ? ORDER BY `users`.`id` ASC LIMIT ?", 45000034, 1),
                new PQuery("SELECT  posts.* FROM `posts` INNER JOIN `share_visibilities` ON `share_visibilities`.`shareable_id` = `posts`.`id` AND `share_visibilities`.`shareable_type` = ? WHERE `posts`.`id` = ? AND `share_visibilities`.`user_id` = ? ORDER BY `posts`.`id` ASC LIMIT ?", "Post", 33000073, 45000034, 1),
                new PQuery("SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = ? LIMIT ?", 45000034, 1),
                new PQuery("SELECT `mentions`.`id` FROM `mentions` WHERE `mentions`.`mentions_container_id` = ? AND `mentions`.`mentions_container_type` = ? AND `mentions`.`person_id` = ?", 33000073, "Post", 26000035),
                new PQuery("SELECT `mentions`.`id` FROM `mentions` INNER JOIN comments ON mentions.mentions_container_id = comments.id AND mentions.mentions_container_type = 'Comment' WHERE `comments`.`commentable_id` = ? AND `comments`.`commentable_type` = ?", 33000073, "Post"),
                new PQuery("SELECT `mentions`.* FROM `mentions` WHERE `mentions`.`mentions_container_id` = ? AND `mentions`.`mentions_container_type` = ?", 33000073, "Post"),
                new PQuery("SELECT  `people`.* FROM `people` WHERE `people`.`id` = ? LIMIT ?", 26000003, 1),
                new PQuery("SELECT  profiles.id, profiles.diaspora_handle, profiles.first_name, profiles.last_name, profiles.image_url, profiles.image_url_small, profiles.image_url_medium, profiles.searchable, profiles.person_id, profiles.created_at, profiles.updated_at, profiles.full_name, profiles.nsfw, profiles.public_details FROM `profiles` WHERE `profiles`.`person_id` = ? LIMIT ?", 26000003, 1),
                new PQuery("SELECT `photos`.* FROM `photos` WHERE `photos`.`status_message_guid` = ?", "b2eb78a08ed7013960787145d8247422"),
                new PQuery("SELECT  `locations`.* FROM `locations` WHERE `locations`.`status_message_id` = ? LIMIT ?", 33000073, 1),
                new PQuery("SELECT  `polls`.* FROM `polls` WHERE `polls`.`status_message_id` = ? LIMIT ?", 33000073, 1),
                new PQuery("SELECT  1 AS one_ FROM `participations` WHERE `participations`.`author_id` = ? AND `participations`.`target_id` = ? LIMIT ?", 26000035, 33000073, 1),
        };
        testQueries(queries, 45000034, 2);
    }

    @Test
    public void testMyProfile() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("SELECT  `users`.* FROM `users` WHERE `users`.`id` = ? ORDER BY `users`.`id` ASC LIMIT ?", 45000034, 1),
                new PQuery("SELECT  `people`.* FROM `people` WHERE `people`.`guid` = ? LIMIT ?", "30c2ef608e5c0139d94f011df6dc47b7", 1),
                new PQuery("SELECT `notifications`.* FROM `notifications` WHERE `notifications`.`recipient_id` = ? AND `notifications`.`target_type` = ? AND `notifications`.`target_id` = ? AND `notifications`.`unread` = ?", 45000034, "Person", 26000034, true),
                new PQuery("SELECT  `contacts`.* FROM `contacts` WHERE `contacts`.`user_id` = ? AND `contacts`.`person_id` = ? LIMIT ?", 45000034, 26000034, 1),
                new PQuery("SELECT  profiles.id, profiles.diaspora_handle, profiles.first_name, profiles.last_name, profiles.image_url, profiles.image_url_small, profiles.image_url_medium, profiles.searchable, profiles.person_id, profiles.created_at, profiles.updated_at, profiles.full_name, profiles.nsfw, profiles.public_details FROM `profiles` WHERE `profiles`.`person_id` = ? LIMIT ?", 26000034, 1),
                new PQuery("SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = ? LIMIT ?", 45000034, 1),
                new PQuery("SELECT  `blocks`.* FROM `blocks` WHERE `blocks`.`user_id` = ? AND `blocks`.`person_id` = ? LIMIT ?", 45000034, 26000034, 1),
                new PQuery("SELECT `tags`.`name` FROM `tags` INNER JOIN `taggings` ON `tags`.`id` = `taggings`.`tag_id` WHERE `taggings`.`taggable_id` = ? AND `taggings`.`taggable_type` = ? AND `taggings`.`context` = ? ORDER BY taggings.id", 34000034, "Profile", "tags"),
                new PQuery("SELECT COUNT(*) FROM (SELECT DISTINCT photos.* FROM `photos` LEFT OUTER JOIN share_visibilities ON share_visibilities.shareable_id = photos.id AND share_visibilities.shareable_type = 'Photo' WHERE `photos`.`author_id` = ? AND (`share_visibilities`.`user_id` = 45000034 OR `photos`.`public` = 1) AND (photos.created_at < '2021-10-16 23:26:55.497129') AND `photos`.`pending` = ? ORDER BY photos.created_at DESC, created_at DESC) subquery_for_count", 26000034, false),
        };
        testQueries(queries, 45000034, 5);
    }

    @Test
    public void testMyProfileStream() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("SELECT  `users`.* FROM `users` WHERE `users`.`id` = ? ORDER BY `users`.`id` ASC LIMIT ?", 45000034, 1),
                new PQuery("SELECT  `people`.* FROM `people` WHERE `people`.`guid` = ? LIMIT ?", "30c2ef608e5c0139d94f011df6dc47b7", 1),
                new PQuery("SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = ? LIMIT ?", 45000034, 1),
                new PQuery("SELECT  DISTINCT posts.* FROM `posts` LEFT OUTER JOIN share_visibilities ON share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' WHERE `posts`.`author_id` = ? AND (`share_visibilities`.`user_id` = 45000034 OR `posts`.`public` = 1) AND (posts.created_at < '2021-10-17 04:22:41') AND `posts`.`type` IN (?, ?) ORDER BY posts.created_at desc, posts.created_at DESC, posts.id DESC LIMIT ?", 26000034, "StatusMessage", "Reshare", 15),
        };
        testQueries(queries, 45000034, 1);
    }

    @Test
    public void testConversation() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("SELECT  `users`.* FROM `users` WHERE `users`.`id` = ? ORDER BY `users`.`id` ASC LIMIT ?", 45000034, 1),
                new PQuery("SELECT  `people`.* FROM `people` WHERE `people`.`owner_id` = ? LIMIT ?", 45000034, 1),
                new PQuery("SELECT  `conversations`.* FROM `conversations` INNER JOIN `conversation_visibilities` ON `conversation_visibilities`.`conversation_id` = `conversations`.`id` WHERE `conversation_visibilities`.`person_id` = ? AND `conversation_visibilities`.`conversation_id` = ? ORDER BY `conversations`.`id` ASC LIMIT ?", 26000035, 12000002, 1),
                new PQuery("SELECT  `conversation_visibilities`.* FROM `conversation_visibilities` WHERE `conversation_visibilities`.`conversation_id` = ? AND `conversation_visibilities`.`person_id` = ? AND (unread > 0) ORDER BY `conversation_visibilities`.`id` ASC LIMIT ?", 12000002, 26000035, 1),
                new PQuery("SELECT  `conversation_visibilities`.* FROM `conversation_visibilities` WHERE `conversation_visibilities`.`conversation_id` = ? AND `conversation_visibilities`.`person_id` = ? LIMIT ?", 12000002, 26000035, 1),
                new PQuery("SELECT  `people`.* FROM `people` WHERE `people`.`id` = ? LIMIT ?", 26000035, 1),
                new PQuery("SELECT contacts.id, profiles.first_name, profiles.last_name, people.diaspora_handle FROM `contacts` INNER JOIN `people` ON `people`.`id` = `contacts`.`person_id` INNER JOIN `profiles` ON `profiles`.`person_id` = `people`.`id` WHERE `contacts`.`user_id` = ? AND `contacts`.`sharing` = ? AND `contacts`.`receiving` = ?", 45000034, true, true),
                new PQuery("SELECT  1 AS one_ FROM `contacts` WHERE `contacts`.`user_id` = ? AND `contacts`.`sharing` = ? AND `contacts`.`receiving` = ? LIMIT ?", 45000034, true, true, 1),
                new PQuery("SELECT COUNT(*) FROM (SELECT DISTINCT `conversation_visibilities`.`id` FROM `conversation_visibilities` LEFT OUTER JOIN `conversations` ON `conversations`.`id` = `conversation_visibilities`.`conversation_id` WHERE `conversation_visibilities`.`person_id`= ?) subquery_for_count", 26000035),
                new PQuery("SELECT  `conversation_visibilities`.`id` AS t0_r0, `conversation_visibilities`.`conversation_id` AS t0_r1, `conversation_visibilities`.`person_id` AS t0_r2, `conversation_visibilities`.`unread` AS t0_r3, `conversation_visibilities`.`created_at` AS t0_r4, `conversation_visibilities`.`updated_at` AS t0_r5, `conversations`.`id` AS t1_r0, `conversations`.`subject` AS t1_r1, `conversations`.`guid` AS t1_r2, `conversations`.`author_id` AS t1_r3, `conversations`.`created_at` AS t1_r4, `conversations`.`updated_at` AS t1_r5 FROM `conversation_visibilities` LEFT OUTER JOIN `conversations` ON `conversations`.`id` = `conversation_visibilities`.`conversation_id` WHERE `conversation_visibilities`.`person_id` = ? ORDER BY conversations.updated_at DESC LIMIT ? OFFSET ?", 26000035, 1, 1),
        };
        testQueries(queries, 45000034, 1);
    }

    private record PQuery(String query, Object... params) { }
}
