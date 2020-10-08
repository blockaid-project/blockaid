package fatjdbc;

import org.apache.calcite.adapter.java.JavaTypeFactory;
import org.apache.calcite.avatica.AvaticaConnection;
import org.apache.calcite.avatica.AvaticaDatabaseMetaData;
import org.apache.calcite.avatica.AvaticaPreparedStatement;
import org.apache.calcite.avatica.AvaticaResultSet;
import org.apache.calcite.avatica.AvaticaResultSetMetaData;
import org.apache.calcite.avatica.AvaticaStatement;
import org.apache.calcite.avatica.Meta;
import org.apache.calcite.avatica.QueryState;
import org.apache.calcite.jdbc.CalciteRootSchema;

import java.sql.ResultSetMetaData;
import java.sql.SQLException;
import java.sql.SQLFeatureNotSupportedException;
import java.util.Properties;
import java.util.TimeZone;

/**
 * Implementation of {@link org.apache.calcite.avatica.AvaticaFactory} for Drill
 * and
 * JDBC 4.1 (corresponds to JDK 1.7).
 */
public class PrivacyJdbc41Factory extends PrivacyJdbcFactory {

  /**
   * Creates a factory for JDBC version 4.1.
   */
  public PrivacyJdbc41Factory() {
    this(4, 1);
  }

  /**
   * Creates a JDBC factory with given major/minor version number.
   */
  protected PrivacyJdbc41Factory(int major, int minor) {
    super(major, minor);
  }


  @Override
  protected PrivacyConnectionImpl newConnection(PrivacyDriver driver,
                                                PrivacyJdbcFactory factory,
                                                String url,
                                                Properties info,
                                                CalciteRootSchema rootSchema,
                                                JavaTypeFactory typeFactory) throws SQLException {
    return new PrivacyConnectionImpl(driver, factory, url, info, rootSchema, typeFactory);
  }

  public QuarkJdbc41DatabaseMetaData newDatabaseMetaData(
          AvaticaConnection connection) {
    return new QuarkJdbc41DatabaseMetaData(
            (PrivacyConnectionImpl) connection);
  }

  @Override
  public PrivacyStatement newStatement(AvaticaConnection connection,
                                       Meta.StatementHandle statementHandle,
                                       int resultSetType,
                                       int resultSetConcurrency,
                                       int resultSetHoldability) {
    return new QuarkJdbc41Statement((PrivacyConnectionImpl) connection,
            statementHandle,
            resultSetType,
            resultSetConcurrency,
            resultSetHoldability);
  }

  @Override
  public AvaticaResultSet newResultSet(AvaticaStatement statement,
                                       QueryState state,
                                       Meta.Signature signature,
                                       TimeZone timeZone,
                                       Meta.Frame firstFrame) throws SQLException {
    final ResultSetMetaData metaData =
            newResultSetMetaData(statement, signature);
    return new PrivacyResultSet(statement, signature, metaData, timeZone,
            firstFrame);
  }

  @Override
  public AvaticaPreparedStatement newPreparedStatement(AvaticaConnection connection,
                                                       Meta.StatementHandle h,
                                                       Meta.Signature signature,
                                                       int resultSetType,
                                                       int resultSetConcurrency,
                                                       int resultSetHoldability)
          throws SQLException {
    return new PrivacyJdbc41Statement(connection, h, signature, resultSetType,
            resultSetConcurrency, resultSetHoldability);
    //throw new SQLFeatureNotSupportedException();
  }

  @Override
  public ResultSetMetaData newResultSetMetaData(AvaticaStatement statement,
                                                Meta.Signature signature) {
    return new AvaticaResultSetMetaData(statement, null, signature);
  }

  private static class PrivacyJdbc41Statement extends AvaticaPreparedStatement {
    PrivacyJdbc41Statement(AvaticaConnection connection,
                           Meta.StatementHandle h,
                           Meta.Signature signature,
                           int resultSetType,
                           int resultSetConcurrency,
                           int resultSetHoldability) throws SQLException {
      super(connection, h, signature, resultSetType, resultSetConcurrency, resultSetHoldability);
    }
  }

  /**
   * Implementation of statement for JDBC 4.1.
   */
  private static class QuarkJdbc41Statement extends PrivacyStatement {
    QuarkJdbc41Statement(PrivacyConnectionImpl connection,
                         Meta.StatementHandle h,
                         int resultSetType,
                         int resultSetConcurrency,
                         int resultSetHoldability) {
      super(connection, h, resultSetType, resultSetConcurrency,
              resultSetHoldability);
    }
  }

  /**
   * Implementation of database metadata for JDBC 4.1.
   */
  private static class QuarkJdbc41DatabaseMetaData
          extends AvaticaDatabaseMetaData {
    QuarkJdbc41DatabaseMetaData(PrivacyConnectionImpl connection) {
      super(connection);
    }
  }

}