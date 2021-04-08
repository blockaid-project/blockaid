package server;

import edu.berkeley.cs.netsys.privacy_proxy.jdbc.ThinClientUtil;
import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;

import org.flywaydb.core.Flyway;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.IOException;
import java.net.URISyntaxException;
import java.sql.*;
import java.util.*;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.equalTo;

public class EndToEndTest {
    protected static final Log LOG = LogFactory.getLog(Main.class);

    public static String dbUrl = "jdbc:h2:mem:DbTpcds;DB_CLOSE_DELAY=-1";
    public static Main main;
    public static String h2Url = "jdbc:h2:mem:DbServerTpcdsTest;DB_CLOSE_DELAY=-1";
    public static String cubeUrl = "jdbc:h2:mem:DbServerTpcdsCubes;DB_CLOSE_DELAY=-1";
    public static String viewUrl = "jdbc:h2:mem:DbServerTpcdsViews;DB_CLOSE_DELAY=-1";

    @BeforeClass
    public static void setUp() throws SQLException, IOException, URISyntaxException,
            ClassNotFoundException {

        String[] args = new String [1];
        args[0] = server.EndToEndTest.class.getResource("/EndToEndTest/dbCatalog.json").getPath();
        main = new Main(args);

        new Thread(main).start();

        Flyway flyway = new Flyway();
        flyway.setDataSource(dbUrl, "sa", "");
        flyway.migrate();

        setupTables(dbUrl, "tpcds_db.sql");
        setupTables(h2Url, "tpcds.sql");
        setupTables(cubeUrl, "tpcds_cubes.sql");
        setupTables(viewUrl, "tpcds_views.sql");
    }

    public static void setupTables(String dbUrl, String filename)
            throws ClassNotFoundException, SQLException, IOException, URISyntaxException {

        Class.forName("org.h2.Driver");
        Properties props = new Properties();
        props.setProperty("user", "sa");
        props.setProperty("password", "");

        Connection connection = DriverManager.getConnection(dbUrl, props);

        Statement stmt = connection.createStatement();
        java.net.URL url = EndToEndTest.class.getResource("/EndToEndTest/" + filename);
        java.nio.file.Path resPath = java.nio.file.Paths.get(url.toURI());
        String sql = new String(java.nio.file.Files.readAllBytes(resPath), "UTF8");

        stmt.execute(sql);
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
                    throw new RuntimeException(e);
                }
            }
        }

        String query = "select * from canonical.public.web_returns";
        ResultSet resultSet = connection.createStatement().executeQuery(query);

        List<String> wrItemSk = new ArrayList<String>();
        List<String> wrOrderNumber = new ArrayList<String>();
        while (resultSet.next()) {
            wrItemSk.add(resultSet.getString("wr_item_sk"));
            wrOrderNumber.add(resultSet.getString("wr_order_number"));
        }

        assertThat(wrItemSk.size(), equalTo(1));
        assertThat(wrOrderNumber.size(), equalTo(1));
        assertThat(wrItemSk.get(0), equalTo("1"));
        assertThat(wrOrderNumber.get(0), equalTo("10"));
    }
}
