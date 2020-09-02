package fatjdbc;

import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;

import java.io.IOException;
import java.net.URISyntaxException;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.equalTo;

public class HotCrpIntegTest extends IntegTest {
  public static final String h2Url = "jdbc:h2:mem:HotCRPTest;DB_CLOSE_DELAY=-1";
  public static Connection conn;


  @BeforeClass
  public static void setUpClass() throws ClassNotFoundException, SQLException,
          IOException, URISyntaxException {
    setupTables(h2Url, "hotcrp.sql");

    Class.forName("fatjdbc.PrivacyDriver");
    conn = DriverManager.getConnection("jdbc:privacy:fat:json:"
            + TpcdsIntegTest.class.getResource("/HotCRPModel.json").getPath(), new Properties());
  }

  @Test
  public void simpleAggregateCountQuery() throws SQLException, ClassNotFoundException {

    String query = "select count(*) from PaperStorage";
    ResultSet rs1 = conn.createStatement().executeQuery(query);
//
//    String parsedQuery = "select count(*) from public.web_returns";
//
//    ResultSet rs2 = executeQuery(h2Url, parsedQuery);
//
//    checkSameResultSet(rs1, rs2);
  }
}
