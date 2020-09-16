package fatjdbc;

import catalog.db.encryption.AESEncrypt;
import fatjdbc.utility.YCSBTest;
import org.flywaydb.core.Flyway;
import org.junit.BeforeClass;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.Statement;
import java.util.Properties;

/**
 * Created by adeshr on 2/18/16.
 */
public class DbYCSBTest extends YCSBTest {
    private static final String dbSchemaUrl = "jdbc:h2:mem:DbSelectTest;DB_CLOSE_DELAY=-1";
    private static Connection dbConnection;
    static {
        dbUrl = "jdbc:h2:mem:SelectTest2;DB_CLOSE_DELAY=-1";
        props = new Properties();
        props.put("url", dbSchemaUrl);
        props.put("user", "sa");
        props.put("password", "");
        props.put("encryptionKey", "easy");
        props.put("userRole", "controller");
    }

    @BeforeClass
    public static void setUpDb() throws Exception {
        //org.apache.log4j.BasicConfigurator.configure();
        YCSBTest.setUpClass(dbUrl);
        Flyway flyway = new Flyway();
        flyway.setDataSource(dbSchemaUrl, "sa", "");
        flyway.migrate();

        System.out.println("flyway migration completed");

        Properties connInfo = new Properties();
        connInfo.setProperty("url", dbSchemaUrl);
        connInfo.setProperty("user", "sa");
        connInfo.setProperty("password", "");

        dbConnection = DriverManager.getConnection(dbSchemaUrl, connInfo);

        Statement stmt = dbConnection.createStatement();
        String sql = "insert into data_sources(name, type, url, ds_set_id, datasource_type) values "
                + "('H2', 'H2', '" + dbUrl + "', 1, 'JDBC'); insert into jdbc_sources (id, "
                + "username, password) values(1, 'sa', '');" +
                "update ds_sets set default_datasource_id = 1 where id = 1;";

        stmt.execute(sql);
        stmt.close();
    }

    protected String getConnectionUrl() {
        return "jdbc:privacy:fat:db:";
    }
}

