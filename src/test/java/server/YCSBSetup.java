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

public class YCSBSetup {
    public static String dbUrl = "jdbc:h2:mem:DbYCSB;DB_CLOSE_DELAY=-1";
    public static String h2Url = "jdbc:h2:mem:DbServerYCSBTest;DB_CLOSE_DELAY=-1";

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
        stmt.execute(sql);
    }

    public static void main(String[] argv) throws Exception {
        Class.forName("jdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        String[] args = new String [1];
        args[0] = server.EndToEndTest.class.getResource("/YCSB/YCSB.json").getPath();
        Main main = new Main(args);

        new Thread(main).start();

        Flyway flyway = new Flyway();
        flyway.setDataSource(dbUrl, "sa", "");
        flyway.migrate();

        setupTables(dbUrl, "YCSB_db.sql");
        setupTables(h2Url, "YCSB.sql");

        System.out.println("server started");

        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            main.getServer().stop();
            System.out.println("server stopped");
        }));

        Thread.sleep(Long.MAX_VALUE);
    }
}
