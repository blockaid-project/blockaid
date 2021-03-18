package client;

import jdbc.PrivacyConnection;
import org.flywaydb.core.Flyway;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.sql.*;
import java.util.*;

public class FacebookPolicyQueryGeneration {
    private static final int ITERATIONS = 1700;

    private static String dbUsername = "sa";
    private static String dbPassword = "";

    private static final List<String> TABLES = Arrays.asList(
        "users", "friends", "photos", "photo_tags"
    );

    private static final List<String> COLUMNS = Arrays.asList(
            "users.uid", "users.about_me", "users.activities", "users.allowed_restrictions", "users.name", "users.sex",
            "users.books", "users.movies", "users.music", "users.birthday", "users.birthday_date", "users.contact_email",
            "users.can_message", "users.can_post", "users.first_name", "users.has_timeline", "users.install_type",
            "users.interests", "users.is_app_user", "users.is_blocked", "users.is_minor", "users.last_name",
            "users.middle_name", "users.name_format", "friends.uid1", "friends.uid2", "photos.pid", "photos.src",
            "photos.owner", "photos.modified", "photo_tags.subject", "photo_tags.pid", "photo_tags.created",
            "photo_tags.xcoord", "photo_tags.ycoord"
    );

    private static final List<String> FK_CONSTRAINTS = Arrays.asList(
            "friends.uid1 = users.uid",
            "photos.owner = users.uid",
            "photo_tags.subject = users.uid",
            "photo_tags.pid = photos.pid"
    );

    private static final int MAX_NUM_PREDICATES = 3;
    private static final int VALUE_MAX = 10000;

    private static final List<String> COLUMN_TABLE = new ArrayList<>();
    private static final List<String> FK_LEFT = new ArrayList<>();
    private static final List<String> FK_RIGHT = new ArrayList<>();

    static {
        for (String x : COLUMNS) {
            COLUMN_TABLE.add(x.split("\\.")[0]);
        }
        for (String x : FK_CONSTRAINTS) {
            String[] parts = x.split(" = ");
            FK_LEFT.add(parts[0].split("\\.")[0]);
            FK_RIGHT.add(parts[1].split("\\.")[0]);
        }
    }

    private String proxyUrl;

    @Rule
    public TemporaryFolder tempFolder = new TemporaryFolder();

    private static int randomInt(int n) {
        return (int) (Math.random() * n);
    }

    private static List<Integer> randomFromRangeWithoutReplacement(int n, int count) {
        List<Integer> s = new ArrayList<>();
        for (int i = 0; i < n; ++i) {
            s.add(i);
        }
        Collections.shuffle(s);
        return s.subList(0, count);
    }

    private static String generatePredicate(String column) {
        int constant = randomInt(VALUE_MAX);
        switch (randomInt(6)) {
            case 0:
                return column + " < " + constant;
            case 1:
                return column + " <= " + constant;
            case 2:
                return column + " > " + constant;
            case 3:
                return column + " >= " + constant;
            case 4:
                return column + " = " + constant;
            case 5:
                return column + " <> " + constant;
            default:
                throw new RuntimeException("bad operation number");
        }
    }

    private static String combinePredicates(List<String> predicates) {
        if (predicates.size() == 0) {
            return null;
        }
        List<String> remaining = new ArrayList<>(predicates);
        while (remaining.size() > 1) {
            int i = randomInt(remaining.size() - 1);
            String op = (randomInt(2) == 0 ? " AND " : " OR ");
            String combined = "(" + remaining.get(i) + ")" + op + "(" + remaining.get(i + 1) + ")";
            remaining.remove(i + 1);
            remaining.set(i, combined);
        }
        return "(" + remaining.get(0) + ")";
    }

    private static String generateQuery() {
        int targetTableCount = randomInt(TABLES.size()) + 1;

        Set<String> tables = new HashSet<>();
        Set<String> qualifiedTables = new HashSet<>();
        Set<String> constraints = new HashSet<>();

        tables.add(TABLES.get(randomInt(TABLES.size())));
        for (int i = 1; i < targetTableCount; ++i) {
            List<Integer> validConstraints = new ArrayList<>();
            for (int j = 0; j < FK_CONSTRAINTS.size(); ++j) {
                boolean b1 = tables.contains(FK_LEFT.get(j));
                boolean b2 = tables.contains(FK_RIGHT.get(j));
                if (b1 != b2) {
                    validConstraints.add(i);
                }
            }
            if (validConstraints.isEmpty()) {
                break;
            }
            int constraint = validConstraints.get(randomInt(validConstraints.size()));
            tables.add(FK_LEFT.get(constraint));
            tables.add(FK_RIGHT.get(constraint));
            constraints.add(FK_CONSTRAINTS.get(constraint));
        }

        for (String table : tables) {
            qualifiedTables.add(table);
//            qualifiedTables.add("public." + table);
        }

        List<String> validColumns = new ArrayList<>();
        for (int i = 0; i < COLUMNS.size(); ++i) {
            if (tables.contains(COLUMN_TABLE.get(i))) {
                validColumns.add(COLUMNS.get(i));
            }
        }

        int numProjectColumnCount = randomInt(validColumns.size()) + 1;
        List<String> columns = new ArrayList<>();
        for (Integer i : randomFromRangeWithoutReplacement(validColumns.size(), numProjectColumnCount)) {
            columns.add(validColumns.get(i));
        }

        int numSelectConstraintCount = randomInt(MAX_NUM_PREDICATES);
        List<String> predicates = new ArrayList<>();
        for (int i = 0; i < numSelectConstraintCount; ++i) {
            predicates.add(generatePredicate(validColumns.get(randomInt(validColumns.size()))));
        }

        String combinedPredicates = combinePredicates(predicates);
        StringBuilder query = new StringBuilder();
        query.append("SELECT ")
             .append(String.join(", ", columns))
             .append(" FROM ")
             .append(String.join(", ", qualifiedTables))
             .append(" WHERE TRUE");
        for (String constraint : constraints) {
            query.append(" AND ").append(constraint);
        }
        if (combinedPredicates != null) {
            query.append(" AND ").append(combinedPredicates);
        }
        return query.toString();
    }

    private String generateDBSQL(String h2Url) {
        StringBuilder sql = new StringBuilder();
        // not escaped but oh well
        sql.append("INSERT INTO data_sources VALUES(1, 'H2', '").append(h2Url).append("',1,0,'CANONICAL','JDBC',NULL,NULL,NULL);\n");
        sql.append("INSERT INTO jdbc_sources VALUES(1, '").append(dbUsername).append("','").append(dbPassword).append("');\n");
        sql.append("UPDATE ds_sets SET default_datasource_id = 1 WHERE id = 1;\n");
        System.out.println(sql);
        return sql.toString();
    }

    private String generateSchemaSQL() {
        StringBuilder sql = new StringBuilder();
        for (String s : TABLES) {
            sql.append("CREATE TABLE ").append(s).append("(");

            boolean first = true;
            for (int i = 0; i < COLUMNS.size(); ++i) {
                if (COLUMN_TABLE.get(i).equals(s)) {
                    if (!first) {
                        sql.append(",");
                    }
                    sql.append(COLUMNS.get(i).split("\\.")[1]).append(" INTEGER NOT NULL");
                    first = false;
                }
            }

            sql.append(");\n");
        }
        System.out.println(sql);
        return sql.toString();
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
        java.net.URL url = FacebookPolicyQueryGeneration.class.getResource("/FacebookPolicyTest/policies_allow_all.sql");
//        java.net.URL url = FacebookPolicyQueryGeneration.class.getResource("/FacebookPolicyTest/policies.sql");
        java.nio.file.Path resPath = java.nio.file.Paths.get(url.toURI());
        java.net.URL pk_url = FacebookPolicyQueryGeneration.class.getResource("/FacebookPolicyTest/pk.txt");
        java.nio.file.Path pk_resPath = java.nio.file.Paths.get(pk_url.toURI());
        java.net.URL fk_url = FacebookPolicyQueryGeneration.class.getResource("/FacebookPolicyTest/fk.txt");
        java.nio.file.Path fk_resPath = java.nio.file.Paths.get(fk_url.toURI());
        java.net.URL deps_url = FacebookPolicyQueryGeneration.class.getResource("/FacebookPolicyTest/deps.txt");
        java.nio.file.Path deps_resPath = java.nio.file.Paths.get(deps_url.toURI());

        String dbFile = tempFolder.newFile("Db").getPath();
        String h2File = tempFolder.newFile("DbServer").getPath();
        String dbUrl = "jdbc:h2:" + dbFile;
        String h2Url = "jdbc:h2:" + h2File;
        proxyUrl = "jdbc:privacy:thin:" + resPath.toString() + "," + deps_resPath.toString() + "," + dbUrl + "," + h2Url + "," + pk_resPath.toString()+ "," + fk_resPath.toString();

        Flyway flyway = new Flyway();
        flyway.setDataSource(dbUrl, dbUsername, dbPassword);
        flyway.migrate();

        setupTables(dbUrl, generateDBSQL(h2Url));
        setupTables(h2Url, generateSchemaSQL());
    }

    @Test
    public void runQueryGeneration() throws Exception {
        Class.forName("jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        Connection conn = DriverManager.getConnection(proxyUrl, dbUsername, dbPassword);
        conn.setAutoCommit(true);

        // todo: data needs to be generated or we're querying an empty database

        for (int i = 0; i < ITERATIONS; ++i) {
            String query = generateQuery();
//            System.err.println(query);
            PrivacyConnection.PrivacyPreparedStatement stmt = (PrivacyConnection.PrivacyPreparedStatement) conn.prepareStatement(query);
            long startTime = System.nanoTime();
            stmt.checkPolicy();
//            System.err.println("decision: " + stmt.checkPolicy());
            long endTime = System.nanoTime();
            System.err.println((endTime - startTime) / 1e6);
//            PreparedStatement stmt = conn.prepareStatement(query);
//            ResultSet s = stmt.executeQuery();
//            s.close();
//            stmt.close();
        }
    }
}
