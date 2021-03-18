package client;

import jdbc.PrivacyConnection;
import org.flywaydb.core.Flyway;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import server.EndToEndTest;

import java.nio.charset.StandardCharsets;
import java.sql.*;
import java.util.Properties;

import static org.junit.Assert.assertEquals;

public class FacebookPolicyTest {
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
        System.out.println(sql);
        return sql.toString();
    }

    private String readSchemaSQL() throws Exception {
        java.net.URL url = EndToEndTest.class.getResource("/FacebookPolicyTest/schema.sql");
        java.nio.file.Path resPath = java.nio.file.Paths.get(url.toURI());
        String sql = new String(java.nio.file.Files.readAllBytes(resPath), StandardCharsets.UTF_8);

        System.out.println(sql);
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
        java.net.URL url = EndToEndTest.class.getResource("/FacebookPolicyTest/policies.sql");
        java.nio.file.Path resPath = java.nio.file.Paths.get(url.toURI());
        java.net.URL pk_url = EndToEndTest.class.getResource("/FacebookPolicyTest/pk.txt");
        java.nio.file.Path pk_resPath = java.nio.file.Paths.get(pk_url.toURI());
        java.net.URL fk_url = EndToEndTest.class.getResource("/FacebookPolicyTest/fk.txt");
        java.nio.file.Path fk_resPath = java.nio.file.Paths.get(fk_url.toURI());
        java.net.URL deps_url = EndToEndTest.class.getResource("/FacebookPolicyTest/deps.txt");
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

    private void testQuery(Connection connection, String query, boolean expected) throws SQLException {
        PrivacyConnection.PrivacyPreparedStatement p = (PrivacyConnection.PrivacyPreparedStatement) connection.prepareStatement(query);
        assertEquals(expected, p.checkPolicy());
    }

    @Test
    public void runQueryGeneration() throws Exception {
        Class.forName("jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        // todo: data needs to be generated or we're querying an empty database

        // Some arbitrary other user's name -- obviously non-compliant.
        testQuery(conn, "SELECT name FROM users WHERE uid = _OTHER_UID", false);
        // Friends' birthday -- picked straight from a permission.
        testQuery(conn, "SELECT users.birthday, users.birthday_date FROM users, friends WHERE friends.uid1 = _MY_UID AND friends.uid2 = users.uid", true);
        // Current user's birthday and likes -- possibly compliant due to primary key constraint.
        testQuery(conn, "SELECT birthday_date, music, movies FROM users WHERE uid = _MY_UID", true);
        // Friends' likes through UID2 -- possibly compliant due to symmetry constraint.
        testQuery(conn, "SELECT users.movies FROM users, friends WHERE friends.uid2 = _MY_UID AND friends.uid1 = users.uid", true);
        // IDs and URLs of photos in which either myself or a friend is tagged -- union of two permission CQs.
//        ~                             | 14     (UnionQuery(
//                ~                             | 15         SCHEMA.make_psj(lambda p, _pt: (p.pid, p.src), from_=("photo", "photo_tag"),
//        ~                             | 16                         where=lambda p, pt: And(p.pid == pt.pid, pt.subject == MY_UID)),
//        ~                             | 17         SCHEMA.make_psj(lambda p, _pt, _f: (p.pid, p.src), from_=("photo", "photo_tag", "friend"),
//        ~                             | 18                         where=lambda p, pt, f: And(f.uid1 == MY_UID, pt.subject == f.uid2, p.pid == pt.pid)),
//        ~                             | 19     ), lambda perms: "user_photos" in perms and "friends_photos" in perms),
        // IDs and URLs of photos in which both myself and a friend are tagged -- self-join
//                ~                             | 21     (SCHEMA.make_psj(lambda p, *_: (p.pid, p.src), from_=("photo", "friend", "photo_tag", "photo_tag"),
//        ~                             | 22                      where=lambda p, f, pt1, pt2: And(
//                ~                             | 23                          p.pid == pt1.pid, pt1.subject == MY_UID,
//                ~                             | 24                          p.pid == pt2.pid, pt2.subject == f.uid2, f.uid1 == MY_UID
//        ~                             | 25                      )),
//        ~                             | 26      lambda perms: "user_photos" in perms and "friends_photos" in perms),
//        ~                             | 27 ]
    }

}
