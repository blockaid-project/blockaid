package client;

import org.flywaydb.core.Flyway;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.sql.*;
import java.util.*;

public class SimpleQueryGeneration {
    private static final int ITERATIONS = 100000;

    private static String dbUsername = "sa";
    private static String dbPassword = "";

    private static final List<String> TABLES = Arrays.asList(
        "table1", "table2", "table3"
    );

    private static final List<String> COLUMNS = Arrays.asList(
        "table1.a", "table1.b", "table1.c",
        "table2.a", "table2.b", "table2.c",
        "table3.a", "table3.b", "table3.c"
    );

    private static final List<String> PK_CONSTRAINTS = Arrays.asList(
            "table1:a",
            "table2:b",
            "table3:c"
    );

    private static final List<String> FK_CONSTRAINTS = Arrays.asList(
            "table2.a = table1.a",
            "table3.a = table1.a",
            "table3.b = table2.b"
    );

    private static final List<String> POLICIES = Arrays.asList(
            "SELECT a, b, c FROM table1",
            "SELECT a, b, c FROM table2",
            "SELECT a, b, c FROM table3"
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
            qualifiedTables.add("public." + table);
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
        String dbFile = tempFolder.newFile("Db").getPath();
        String h2File = tempFolder.newFile("DbServer").getPath();
        String policyFile = tempFolder.newFile("policies.sql").getPath();
        String depsFile = tempFolder.newFile("deps.sql").getPath();
        String pkFile = tempFolder.newFile("pk.txt").getPath();
        String fkFile = tempFolder.newFile("fk.txt").getPath();
        String dbUrl = "jdbc:h2:" + dbFile;
        String h2Url = "jdbc:h2:" + h2File;
        proxyUrl = "jdbc:privacy:thin:" + policyFile + "," + depsFile + "," + dbUrl + "," + h2Url + "," + pkFile + "," + fkFile;

        Flyway flyway = new Flyway();
        flyway.setDataSource(dbUrl, dbUsername, dbPassword);
        flyway.migrate();

        setupTables(dbUrl, generateDBSQL(h2Url));
        setupTables(h2Url, generateSchemaSQL());

        BufferedWriter writer = new BufferedWriter(new FileWriter(policyFile));
        for (String sql : POLICIES) {
            writer.write(sql);
            writer.write(";\n");
        }
        writer.close();
        writer = new BufferedWriter(new FileWriter(depsFile));
        writer.close();
        writer = new BufferedWriter(new FileWriter(pkFile));
        for (String constraint : PK_CONSTRAINTS) {
            writer.write(constraint);
            writer.write(";\n");
        }
        writer.close();
        writer = new BufferedWriter(new FileWriter(fkFile));
        for (String constraint : FK_CONSTRAINTS) {
            writer.write(constraint.replace(" = ", ":"));
            writer.write(";\n");
        }
        writer.close();
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
//            System.out.println(query);
            PreparedStatement stmt = conn.prepareStatement(query);
            ResultSet s = stmt.executeQuery();
            s.close();
            stmt.close();
        }
    }
}
