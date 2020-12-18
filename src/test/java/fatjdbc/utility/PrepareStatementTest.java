package fatjdbc.utility;

import org.junit.AfterClass;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.sql.*;
import java.util.ArrayList;
import java.util.Properties;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Created by rajatv on 10/29/15.
 */
public abstract class PrepareStatementTest {
    private static final Logger log = LoggerFactory.getLogger(SelectTest.class);

    private static Connection h2Connection;
    protected static String dbUrl = "jdbc:h2:mem:SelectTest;DB_CLOSE_DELAY=-1";
    protected static Properties props;

    protected abstract String getConnectionUrl();

    public static void setUpClass(String dbUrl) throws Exception {
        Class.forName("fatjdbc.PrivacyDriver");
        Class.forName("org.h2.Driver");

        Properties connInfo = new Properties();
        connInfo.setProperty("url", dbUrl);
        connInfo.setProperty("user", "sa");
        connInfo.setProperty("password", "");

        h2Connection = DriverManager.getConnection(dbUrl, connInfo);

        Statement stmt = h2Connection.createStatement();
        String sql = "create table simple (i int, j int);"
                + "insert into simple values(1, 4);"
                + "insert into simple values(2, 5);"
                + "insert into simple values(3, 6);";

        stmt.execute(sql);
        stmt.close();
    }

    @AfterClass
    public static void tearDownClass() throws SQLException {
        h2Connection.close();
    }

    @Test
    public void testParametrizedInsert() throws SQLException, ClassNotFoundException {
        Class.forName("fatjdbc.PrivacyDriver");
        Connection connection =
                DriverManager.getConnection(getConnectionUrl(), props);

        //Statement statement = connection.createStatement();
        //String insertQuery = "insert into simple (i,j) values(?,?)";
        String insertQuery = "update simple set i = 100 where j = 100";
        PreparedStatement updateQuery = connection.prepareStatement(insertQuery);

        //updateQuery.setInt(1, 1);
        //updateQuery.setInt(1, 10);
        //updateQuery.setInt(2, 12);
        int rows_affected = updateQuery.executeUpdate();
        assertThat(rows_affected).isEqualTo(0);
        updateQuery.close();
        connection.close();

        /*
        assertThat(firstColumn).contains(1, 2, 3);
        assertThat(secondColumn).contains(4, 5, 6);
        assertThat(totalRows).isEqualTo(3);*/

    }

    //@Test
    public void testParametrizedSelect() throws SQLException, ClassNotFoundException {
        Class.forName("fatjdbc.PrivacyDriver");
        Connection connection =
                DriverManager.getConnection(getConnectionUrl(), props);

        //Statement statement = connection.createStatement();
        String query = "select * from simple where i < ?";
        PreparedStatement updateQuery = connection.prepareStatement(query);
        //ResultSet rows = updateQuery.executeQuery();

        String insertQuery = "insert into simple (i,j) values(5,6)";
        //PreparedStatement updateQuery = connection.prepareStatement(query);

        Statement statement = connection.createStatement();
        //ResultSet rows =
        //        statement.executeQuery("select * from simple where i ");

        updateQuery.setInt(1, 1);
        ResultSet rows = updateQuery.executeQuery();


        //ResultSet rows =
        //        statement.executeQuery("select * from simple");

        ArrayList<Integer> firstColumn = new ArrayList<>();
        ArrayList<Integer> secondColumn = new ArrayList<>();

        assertThat(rows.getMetaData().getColumnCount()).isEqualTo(2);
        int totalRows = 0;
        while (rows.next()) {
            totalRows++;
            firstColumn.add(rows.getInt(1));
            secondColumn.add(rows.getInt(2));
        }
        System.out.println("Total rows is + " + totalRows);
        assertThat(totalRows == 12);
        updateQuery.close();
        connection.close();
        /*
        assertThat(firstColumn).contains(1, 2, 3);
        assertThat(secondColumn).contains(4, 5, 6);
        assertThat(totalRows).isEqualTo(3);*/

    }
}