package server;

import jdbc.ThinClientUtil;
import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.flywaydb.core.Flyway;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.IOException;
import java.net.URISyntaxException;
import java.sql.*;
import java.util.Properties;

import static org.hamcrest.MatcherAssert.assertThat;

public class YCSBSetup {
    protected static final Log LOG = LogFactory.getLog(Main.class);

    public static String dbUrl = "jdbc:h2:mem:DbYCSB;DB_CLOSE_DELAY=-1";
    public static Main main;
    public static String h2Url = "jdbc:h2:mem:DbServerYCSBTest;DB_CLOSE_DELAY=-1";

    @BeforeClass
    public static void setUp() throws SQLException, IOException, URISyntaxException,
            ClassNotFoundException {

        String[] args = new String [1];
        args[0] = server.EndToEndTest.class.getResource("/YCSB/YCSB.json").getPath();
        main = new Main(args);

        new Thread(main).start();

        Flyway flyway = new Flyway();
        flyway.setDataSource(dbUrl, "sa", "");
        flyway.migrate();

        setupTables(dbUrl, "YCSB_db.sql");
        setupTables(h2Url, "YCSB.sql");
    }

    public static void setupTables(String dbUrl, String filename)
            throws ClassNotFoundException, SQLException, IOException, URISyntaxException {

        Class.forName("org.h2.Driver");
        Properties props = new Properties();
        props.setProperty("user", "sa");
        props.setProperty("password", "");

        Connection connection = DriverManager.getConnection(dbUrl, props);

        Statement stmt = connection.createStatement();
        java.net.URL url = EndToEndTest.class.getResource("/YCSB/" + filename);
        java.nio.file.Path resPath = java.nio.file.Paths.get(url.toURI());
        String sql = new String(java.nio.file.Files.readAllBytes(resPath), "UTF8");

        System.out.println(sql);
        stmt.execute(sql);

//        if (sql.contains("create")) {
//            String query = "SELECT * FROM usertable";
//            System.out.println("select" + connection.createStatement().executeQuery(query));
//        }
    }

    @AfterClass
    public static void afterClass() {
        if (main.getServer() != null) {
            main.getServer().stop();
        }
    }

    @Test
    public void testClient() throws SQLException, ClassNotFoundException, InterruptedException {
        Class.forName("jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");
        Connection connection = null;

        // Due to threading, server might not be up.
        for (int i=0; i<2; i++) {
            try {
                connection = DriverManager.getConnection(ThinClientUtil.getConnectionUrl("0.0.0.0", 8765), new Properties());
            } catch (RuntimeException e) {
                if (e.getMessage().contains("Connection refused")) {
                    Thread.sleep(2000);
                } else {
                    throw e;
                }
            }
        }

        String query = "SELECT * FROM canonical.public.usertable";
        ResultSet resultSet = connection.createStatement().executeQuery(query);
    }
}
