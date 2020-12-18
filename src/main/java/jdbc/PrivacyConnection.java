package jdbc;

import org.apache.calcite.sql.SqlKind;
import policy_checker.Policy;
import policy_checker.QueryChecker;
import sql.*;

import java.io.InputStream;
import java.io.Reader;
import java.math.BigDecimal;
import java.net.URL;
import java.sql.*;
import java.sql.Date;
import java.util.*;
import java.util.concurrent.Executor;

class PrivacyConnection implements Connection {
  private Connection direct_connection;
  private Parser parser;
  private final QueryChecker query_checker;
  private ArrayList<Policy> policy_list;

  PrivacyConnection(Connection direct_connection, Properties direct_info) throws SQLException {
    this.direct_connection = direct_connection;
    Properties info = direct_info;
    info.setProperty("schemaFactory", "catalog.db.SchemaFactory");
    this.parser = new ParserFactory(info).getParser(info);

    this.policy_list = new ArrayList<>();
    set_policy(info);
    this.query_checker = new QueryChecker(this.policy_list);
  }

  private void set_policy(Properties info) {
    String token = info.getProperty("userRole");
    String[] sqlpolicy;
    switch(token != null ? token : "no_policy_set"){
      case "controller":
        this.policy_list.add(new Policy(info, "select ycsb_key, field0, field1, field2, field3, field4, field5, field6, field7, field8, field9 from usertable"));
        break;
      case "processor":
        this.policy_list.add(new Policy(info, "select ycsb_key, field0, field1, field2, field3, field4, field5, field6, field7, field8, field9 from usertable"));
        break;
      default:
        this.policy_list.add(new Policy(info, "select ycsb_key, field0, field1, field2, field3, field4, field5, field6, field7, field8, field9 from usertable"));
    }
  }

  private boolean shouldApplyPolicy(SqlKind kind) {
    return kind.equals(SqlKind.SELECT);
  }

  @Override
  public Statement createStatement() throws SQLException {
    return new PrivacyStatement();
  }

  @Override
  public PreparedStatement prepareStatement(String s) throws SQLException {
    if (shouldApplyPolicy(parser.parse(s).getSqlNode().getKind())) {
      return new PrivacyPreparedStatement(s);
    } else {
      return direct_connection.prepareStatement(s);
    }
  }

  @Override
  public CallableStatement prepareCall(String s) throws SQLException {
    return direct_connection.prepareCall(s);
  }

  @Override
  public String nativeSQL(String s) throws SQLException {
    return direct_connection.nativeSQL(s);
  }

  @Override
  public void setAutoCommit(boolean b) throws SQLException {
    direct_connection.setAutoCommit(b);
  }

  @Override
  public boolean getAutoCommit() throws SQLException {
    return direct_connection.getAutoCommit();
  }

  @Override
  public void commit() throws SQLException {
    direct_connection.commit();
  }

  @Override
  public void rollback() throws SQLException {
    direct_connection.rollback();
  }

  @Override
  public void close() throws SQLException {
    direct_connection.close();
  }

  @Override
  public boolean isClosed() throws SQLException {
    return direct_connection.isClosed();
  }

  @Override
  public DatabaseMetaData getMetaData() throws SQLException {
    return direct_connection.getMetaData();
  }

  @Override
  public void setReadOnly(boolean b) throws SQLException {
    direct_connection.setReadOnly(b);
  }

  @Override
  public boolean isReadOnly() throws SQLException {
    return direct_connection.isReadOnly();
  }

  @Override
  public void setCatalog(String s) throws SQLException {
    direct_connection.setCatalog(s);
  }

  @Override
  public String getCatalog() throws SQLException {
    return direct_connection.getCatalog();
  }

  @Override
  public void setTransactionIsolation(int i) throws SQLException {
    direct_connection.setTransactionIsolation(i);
  }

  @Override
  public int getTransactionIsolation() throws SQLException {
    return direct_connection.getTransactionIsolation();
  }

  @Override
  public SQLWarning getWarnings() throws SQLException {
    return direct_connection.getWarnings();
  }

  @Override
  public void clearWarnings() throws SQLException {
    direct_connection.clearWarnings();
  }

  @Override
  public Statement createStatement(int i, int i1) throws SQLException {
    throw new UnsupportedOperationException();
  }

  @Override
  public PreparedStatement prepareStatement(String s, int i, int i1) throws SQLException {
    return direct_connection.prepareStatement(s, i, i1);
  }

  @Override
  public CallableStatement prepareCall(String s, int i, int i1) throws SQLException {
    return direct_connection.prepareCall(s, i, i1);
  }

  @Override
  public Map<String, Class<?>> getTypeMap() throws SQLException {
    return direct_connection.getTypeMap();
  }

  @Override
  public void setTypeMap(Map<String, Class<?>> map) throws SQLException {
    direct_connection.setTypeMap(map);
  }

  @Override
  public void setHoldability(int i) throws SQLException {
    direct_connection.setHoldability(i);
  }

  @Override
  public int getHoldability() throws SQLException {
    return direct_connection.getHoldability();
  }

  @Override
  public Savepoint setSavepoint() throws SQLException {
    return direct_connection.setSavepoint();
  }

  @Override
  public Savepoint setSavepoint(String s) throws SQLException {
    return direct_connection.setSavepoint(s);
  }

  @Override
  public void rollback(Savepoint savepoint) throws SQLException {
    direct_connection.rollback(savepoint);
  }

  @Override
  public void releaseSavepoint(Savepoint savepoint) throws SQLException {
    direct_connection.releaseSavepoint(savepoint);
  }

  @Override
  public Statement createStatement(int i, int i1, int i2) throws SQLException {
    throw new UnsupportedOperationException();
  }

  @Override
  public PreparedStatement prepareStatement(String s, int i, int i1, int i2) throws SQLException {
    return direct_connection.prepareStatement(s, i, i1, i2);
  }

  @Override
  public CallableStatement prepareCall(String s, int i, int i1, int i2) throws SQLException {
    return direct_connection.prepareCall(s, i, i1, i2);
  }

  @Override
  public PreparedStatement prepareStatement(String s, int i) throws SQLException {
    return direct_connection.prepareStatement(s, i);
  }

  @Override
  public PreparedStatement prepareStatement(String s, int[] ints) throws SQLException {
    return direct_connection.prepareStatement(s, ints);
  }

  @Override
  public PreparedStatement prepareStatement(String s, String[] strings) throws SQLException {
    return direct_connection.prepareStatement(s, strings);
  }

  @Override
  public Clob createClob() throws SQLException {
    return direct_connection.createClob();
  }

  @Override
  public Blob createBlob() throws SQLException {
    return direct_connection.createBlob();
  }

  @Override
  public NClob createNClob() throws SQLException {
    return direct_connection.createNClob();
  }

  @Override
  public SQLXML createSQLXML() throws SQLException {
    return direct_connection.createSQLXML();
  }

  @Override
  public boolean isValid(int i) throws SQLException {
    return direct_connection.isValid(i);
  }

  @Override
  public void setClientInfo(String s, String s1) throws SQLClientInfoException {
    direct_connection.setClientInfo(s, s1);
  }

  @Override
  public void setClientInfo(Properties properties) throws SQLClientInfoException {
    direct_connection.setClientInfo(properties);
  }

  @Override
  public String getClientInfo(String s) throws SQLException {
    return direct_connection.getClientInfo(s);
  }

  @Override
  public Properties getClientInfo() throws SQLException {
    return direct_connection.getClientInfo();
  }

  @Override
  public Array createArrayOf(String s, Object[] objects) throws SQLException {
    return direct_connection.createArrayOf(s, objects);
  }

  @Override
  public Struct createStruct(String s, Object[] objects) throws SQLException {
    return direct_connection.createStruct(s, objects);
  }

  @Override
  public void setSchema(String s) throws SQLException {
    direct_connection.setSchema(s);
  }

  @Override
  public String getSchema() throws SQLException {
    return direct_connection.getSchema();
  }

  @Override
  public void abort(Executor executor) throws SQLException {
    direct_connection.abort(executor);
  }

  @Override
  public void setNetworkTimeout(Executor executor, int i) throws SQLException {
    direct_connection.setNetworkTimeout(executor, i);
  }

  @Override
  public int getNetworkTimeout() throws SQLException {
    return direct_connection.getNetworkTimeout();
  }

  @Override
  public <T> T unwrap(Class<T> aClass) throws SQLException {
    return direct_connection.unwrap(aClass);
  }

  @Override
  public boolean isWrapperFor(Class<?> aClass) throws SQLException {
    return direct_connection.isWrapperFor(aClass);
  }

  private class PrivacyPreparedStatement implements PreparedStatement {
    private PreparedStatement direct_statement;
    private ParserResult parser_result;
    private Object[] values;

    PrivacyPreparedStatement(String sql) throws SQLException {
      values = new Object[(sql + " ").split("\\?").length - 1];
      parser_result = parser.parse(sql);
      direct_statement = direct_connection.prepareStatement(sql);
    }

    @Override
    public ResultSet executeQuery() throws SQLException {
      PrivacyQuery privacy_query = PrivacyQueryFactory.createPrivacyQuery(parser_result, values);
      if (shouldApplyPolicy(parser_result.getSqlNode().getKind())) {
        if (!query_checker.checkPolicy(privacy_query)) {
            throw new SQLException("Privacy compliance was not met");
        }
      }

      return direct_statement.executeQuery();
    }

    @Override
    public int executeUpdate() throws SQLException {
      return direct_statement.executeUpdate();
    }

    @Override
    public void setNull(int i, int i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setBoolean(int i, boolean b) throws SQLException {
      direct_statement.setBoolean(i, b);
      values[i - 1] = b;
    }

    @Override
    public void setByte(int i, byte b) throws SQLException {
      direct_statement.setByte(i, b);
      values[i - 1] = b;
    }

    @Override
    public void setShort(int i, short i1) throws SQLException {
      direct_statement.setShort(i, i1);
      values[i - 1] = i1;
    }

    @Override
    public void setInt(int i, int i1) throws SQLException {
      direct_statement.setInt(i, i1);
      values[i - 1] = i1;
    }

    @Override
    public void setLong(int i, long l) throws SQLException {
      direct_statement.setLong(i, l);
      values[i - 1] = l;
    }

    @Override
    public void setFloat(int i, float v) throws SQLException {
      direct_statement.setFloat(i, v);
      values[i - 1] = v;
    }

    @Override
    public void setDouble(int i, double v) throws SQLException {
      direct_statement.setDouble(i, v);
      values[i - 1] = v;
    }

    @Override
    public void setBigDecimal(int i, BigDecimal bigDecimal) throws SQLException {
      direct_statement.setBigDecimal(i, bigDecimal);
      values[i - 1] = bigDecimal;
    }

    @Override
    public void setString(int i, String s) throws SQLException {
      direct_statement.setString(i, s);
      // not really properly escaped todo fix
      values[i - 1] = s;
    }

    @Override
    public void setBytes(int i, byte[] bytes) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setDate(int i, Date date) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setTime(int i, Time time) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setTimestamp(int i, Timestamp timestamp) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setAsciiStream(int i, InputStream inputStream, int i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    @Deprecated
    public void setUnicodeStream(int i, InputStream inputStream, int i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setBinaryStream(int i, InputStream inputStream, int i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void clearParameters() throws SQLException {
      direct_statement.clearParameters();
      for (int i = 0; i < values.length; ++i) {
          values[i] = null;
      }
    }

    @Override
    public void setObject(int i, Object o, int i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setObject(int i, Object o) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public boolean execute() throws SQLException {
      return direct_statement.execute();
    }

    @Override
    public void addBatch() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setCharacterStream(int i, Reader reader, int i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setRef(int i, Ref ref) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setBlob(int i, Blob blob) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setClob(int i, Clob clob) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setArray(int i, Array array) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public ResultSetMetaData getMetaData() throws SQLException {
      return direct_statement.getMetaData();
    }

    @Override
    public void setDate(int i, Date date, Calendar calendar) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setTime(int i, Time time, Calendar calendar) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setTimestamp(int i, Timestamp timestamp, Calendar calendar) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setNull(int i, int i1, String s) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setURL(int i, URL url) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public ParameterMetaData getParameterMetaData() throws SQLException {
      return direct_statement.getParameterMetaData();
    }

    @Override
    public void setRowId(int i, RowId rowId) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setNString(int i, String s) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setNCharacterStream(int i, Reader reader, long l) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setNClob(int i, NClob nClob) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setClob(int i, Reader reader, long l) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setBlob(int i, InputStream inputStream, long l) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setNClob(int i, Reader reader, long l) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setSQLXML(int i, SQLXML sqlxml) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setObject(int i, Object o, int i1, int i2) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setAsciiStream(int i, InputStream inputStream, long l) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setBinaryStream(int i, InputStream inputStream, long l) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setCharacterStream(int i, Reader reader, long l) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setAsciiStream(int i, InputStream inputStream) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setBinaryStream(int i, InputStream inputStream) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setCharacterStream(int i, Reader reader) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setNCharacterStream(int i, Reader reader) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setClob(int i, Reader reader) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setBlob(int i, InputStream inputStream) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setNClob(int i, Reader reader) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setObject(int i, Object o, SQLType sqlType, int i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setObject(int i, Object o, SQLType sqlType) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public long executeLargeUpdate() throws SQLException {
      return direct_statement.executeLargeUpdate();
    }

    @Override
    public ResultSet executeQuery(String s) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public int executeUpdate(String s) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void close() throws SQLException {
      direct_statement.close();
    }

    @Override
    public int getMaxFieldSize() throws SQLException {
      return direct_statement.getMaxFieldSize();
    }

    @Override
    public void setMaxFieldSize(int i) throws SQLException {
      direct_statement.setMaxFieldSize(i);
    }

    @Override
    public int getMaxRows() throws SQLException {
      return direct_statement.getMaxRows();
    }

    @Override
    public void setMaxRows(int i) throws SQLException {
      direct_statement.setMaxRows(i);
    }

    @Override
    public void setEscapeProcessing(boolean b) throws SQLException {
      direct_statement.setEscapeProcessing(b);
    }

    @Override
    public int getQueryTimeout() throws SQLException {
      return direct_statement.getQueryTimeout();
    }

    @Override
    public void setQueryTimeout(int i) throws SQLException {
      direct_statement.setQueryTimeout(i);
    }

    @Override
    public void cancel() throws SQLException {
      direct_statement.cancel();
    }

    @Override
    public SQLWarning getWarnings() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void clearWarnings() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setCursorName(String s) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public boolean execute(String s) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public ResultSet getResultSet() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public int getUpdateCount() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public boolean getMoreResults() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setFetchDirection(int i) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public int getFetchDirection() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setFetchSize(int i) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public int getFetchSize() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public int getResultSetConcurrency() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public int getResultSetType() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void addBatch(String s) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void clearBatch() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public int[] executeBatch() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public Connection getConnection() throws SQLException {
      return PrivacyConnection.this;
    }

    @Override
    public boolean getMoreResults(int i) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public ResultSet getGeneratedKeys() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public int executeUpdate(String s, int i) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public int executeUpdate(String s, int[] ints) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public int executeUpdate(String s, String[] strings) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public boolean execute(String s, int i) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public boolean execute(String s, int[] ints) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public boolean execute(String s, String[] strings) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public int getResultSetHoldability() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public boolean isClosed() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setPoolable(boolean b) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public boolean isPoolable() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void closeOnCompletion() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public boolean isCloseOnCompletion() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public long getLargeUpdateCount() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setLargeMaxRows(long l) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public long getLargeMaxRows() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public long[] executeLargeBatch() throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public long executeLargeUpdate(String s) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public long executeLargeUpdate(String s, int i) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public long executeLargeUpdate(String s, int[] ints) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public long executeLargeUpdate(String s, String[] strings) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public <T> T unwrap(Class<T> aClass) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public boolean isWrapperFor(Class<?> aClass) throws SQLException {
      throw new UnsupportedOperationException();
    }
  }

  private class PrivacyStatement implements Statement {
    private Statement direct_statement;
    private Statement active_statment;

    private PrivacyStatement() throws SQLException {
      this.direct_statement = direct_connection.createStatement();
      this.active_statment = this.direct_statement;
    }


    @Override
    public ResultSet executeQuery(String s) throws SQLException {
      return active_statment.executeQuery(s);
    }

    @Override
    public int executeUpdate(String s) throws SQLException {
      return active_statment.executeUpdate(s);
    }

    @Override
    public void close() throws SQLException {
      active_statment.close();
    }

    @Override
    public int getMaxFieldSize() throws SQLException {
      return active_statment.getMaxFieldSize();
    }

    @Override
    public void setMaxFieldSize(int i) throws SQLException {
      active_statment.setMaxFieldSize(i);
    }

    @Override
    public int getMaxRows() throws SQLException {
      return active_statment.getMaxRows();
    }

    @Override
    public void setMaxRows(int i) throws SQLException {
      active_statment.setMaxRows(i);
    }

    @Override
    public void setEscapeProcessing(boolean b) throws SQLException {
      active_statment.setEscapeProcessing(b);
    }

    @Override
    public int getQueryTimeout() throws SQLException {
      return active_statment.getQueryTimeout();
    }

    @Override
    public void setQueryTimeout(int i) throws SQLException {
      active_statment.setQueryTimeout(i);
    }

    @Override
    public void cancel() throws SQLException {
      active_statment.cancel();
    }

    @Override
    public SQLWarning getWarnings() throws SQLException {
      return active_statment.getWarnings();
    }

    @Override
    public void clearWarnings() throws SQLException {
      active_statment.clearWarnings();
    }

    @Override
    public void setCursorName(String s) throws SQLException {
      active_statment.setCursorName(s);
    }

    @Override
    public boolean execute(String s) throws SQLException {
      return active_statment.execute(s);
    }

    @Override
    public ResultSet getResultSet() throws SQLException {
      return active_statment.getResultSet();
    }

    @Override
    public int getUpdateCount() throws SQLException {
      return active_statment.getUpdateCount();
    }

    @Override
    public boolean getMoreResults() throws SQLException {
      return active_statment.getMoreResults();
    }

    @Override
    public void setFetchDirection(int i) throws SQLException {
      active_statment.setFetchDirection(i);
    }

    @Override
    public int getFetchDirection() throws SQLException {
      return active_statment.getFetchDirection();
    }

    @Override
    public void setFetchSize(int i) throws SQLException {
      active_statment.setFetchSize(i);
    }

    @Override
    public int getFetchSize() throws SQLException {
      return active_statment.getFetchSize();
    }

    @Override
    public int getResultSetConcurrency() throws SQLException {
      return active_statment.getResultSetConcurrency();
    }

    @Override
    public int getResultSetType() throws SQLException {
      return active_statment.getResultSetType();
    }

    @Override
    public void addBatch(String s) throws SQLException {
      active_statment.addBatch(s);
    }

    @Override
    public void clearBatch() throws SQLException {
      active_statment.clearBatch();
    }

    @Override
    public int[] executeBatch() throws SQLException {
      return active_statment.executeBatch();
    }

    @Override
    public Connection getConnection() throws SQLException {
      return active_statment.getConnection();
    }

    @Override
    public boolean getMoreResults(int i) throws SQLException {
      return active_statment.getMoreResults(i);
    }

    @Override
    public ResultSet getGeneratedKeys() throws SQLException {
      return active_statment.getGeneratedKeys();
    }

    @Override
    public int executeUpdate(String s, int i) throws SQLException {
      return active_statment.executeUpdate(s, i);
    }

    @Override
    public int executeUpdate(String s, int[] ints) throws SQLException {
      return active_statment.executeUpdate(s, ints);
    }

    @Override
    public int executeUpdate(String s, String[] strings) throws SQLException {
      return active_statment.executeUpdate(s, strings);
    }

    @Override
    public boolean execute(String s, int i) throws SQLException {
      return active_statment.execute(s, i);
    }

    @Override
    public boolean execute(String s, int[] ints) throws SQLException {
      return active_statment.execute(s, ints);
    }

    @Override
    public boolean execute(String s, String[] strings) throws SQLException {
      return active_statment.execute(s, strings);
    }

    @Override
    public int getResultSetHoldability() throws SQLException {
      return active_statment.getResultSetHoldability();
    }

    @Override
    public boolean isClosed() throws SQLException {
      return active_statment.isClosed();
    }

    @Override
    public void setPoolable(boolean b) throws SQLException {
      active_statment.setPoolable(b);
    }

    @Override
    public boolean isPoolable() throws SQLException {
      return active_statment.isPoolable();
    }

    @Override
    public void closeOnCompletion() throws SQLException {
      active_statment.closeOnCompletion();
    }

    @Override
    public boolean isCloseOnCompletion() throws SQLException {
      return active_statment.isCloseOnCompletion();
    }

    @Override
    public long getLargeUpdateCount() throws SQLException {
      return active_statment.getLargeUpdateCount();
    }

    @Override
    public void setLargeMaxRows(long l) throws SQLException {
      active_statment.setLargeMaxRows(l);
    }

    @Override
    public long getLargeMaxRows() throws SQLException {
      return active_statment.getLargeMaxRows();
    }

    @Override
    public long[] executeLargeBatch() throws SQLException {
      return active_statment.executeLargeBatch();
    }

    @Override
    public long executeLargeUpdate(String s) throws SQLException {
      return active_statment.executeLargeUpdate(s);
    }

    @Override
    public long executeLargeUpdate(String s, int i) throws SQLException {
      return active_statment.executeLargeUpdate(s, i);
    }

    @Override
    public long executeLargeUpdate(String s, int[] ints) throws SQLException {
      return active_statment.executeLargeUpdate(s, ints);
    }

    @Override
    public long executeLargeUpdate(String s, String[] strings) throws SQLException {
      return active_statment.executeLargeUpdate(s, strings);
    }

    @Override
    public <T> T unwrap(Class<T> aClass) throws SQLException {
      return active_statment.unwrap(aClass);
    }

    @Override
    public boolean isWrapperFor(Class<?> aClass) throws SQLException {
      return active_statment.isWrapperFor(aClass);
    }
  }
}
