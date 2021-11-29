package client;

import com.google.common.collect.Iterables;
import edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyConnection;

import java.sql.*;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.Arrays;
import java.util.Map;

import static com.google.common.base.Preconditions.checkArgument;

public class ApplicationTest {
    private final String proxyUrl, dbUsername, dbPassword;

    protected ApplicationTest(String dbName, String dbUsername, String dbPassword, String resourcePath) {
        String dbUrl = "jdbc:mysql://127.0.0.1:3306/" + dbName +
                "?useSSL=false&useUnicode=true&character_set_server=utf8mb4&collation_server=utf8mb4_bin";
        this.proxyUrl = String.format("jdbc:privacy:thin:%s,%s,%s",
                resourcePath,
                dbUrl,
                dbName
        );
        this.dbUsername = dbUsername;
        this.dbPassword = dbPassword;
    }

    protected record PQuery(String query, Object... params) { }

    protected void testQueries(String[] queries, int userId, int numRounds) throws ClassNotFoundException, SQLException {
        testQueries(
                Arrays.stream(queries).map(PQuery::new).toArray(PQuery[]::new),
                userId, numRounds
        );
    }

    protected void testQueries(Iterable<PQuery> queries, int userId, int numRounds) throws ClassNotFoundException, SQLException {
        testQueries(Iterables.toArray(queries, PQuery.class), userId, numRounds);
    }

    protected void testQueries(PQuery[] queries, int userId, int numRounds) throws ClassNotFoundException, SQLException {
        testQueries(queries, Map.of("_MY_UID", userId), numRounds);
    }

    protected void testQueries(PQuery[] queries, Map<String, Object> params, int numRounds) throws ClassNotFoundException, SQLException {
        Class.forName("edu.berkeley.cs.netsys.privacy_proxy.jdbc.PrivacyDriver");
        try (PrivacyConnection conn = (PrivacyConnection) DriverManager.getConnection(proxyUrl, dbUsername, dbPassword)) {
            while (numRounds-- > 0) {
                long startMs = System.currentTimeMillis();
                try (Statement stmt = conn.createStatement()) {
                    for (Map.Entry<String, Object> entry : params.entrySet()) {
                        Object value = entry.getValue();
                        String valueRepr;
                        if (value instanceof String str) {
                            checkArgument(!str.contains("'"));
                            valueRepr = "'" + str + "'";
                        } else if (value instanceof Integer i) {
                            valueRepr = i.toString();
                        } else {
                            throw new IllegalArgumentException("unsupported param value: " + value);
                        }

                        stmt.execute("SET @" + entry.getKey() + " = " + valueRepr);
                    }
                }

                for (PQuery pq : queries) {
                    String q = pq.query;
                    if (q.contains("%1$s")) {
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
}
