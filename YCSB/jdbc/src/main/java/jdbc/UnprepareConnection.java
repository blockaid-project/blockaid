package jdbc;

import java.io.InputStream;
import java.io.Reader;
import java.math.BigDecimal;
import java.net.URL;
import java.sql.*;
import java.util.Calendar;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.Executor;

// a big hack to convert prepared statements that YCSB uses to non-prepared statement
public class UnprepareConnection implements Connection {
  Connection connection;

  public UnprepareConnection(Connection connection) {
    this.connection = connection;
  }

  @Override
  public Statement createStatement() throws SQLException {
    return connection.createStatement();
  }

  @Override
  public PreparedStatement prepareStatement(String s) throws SQLException {
    return new UnpreparedStatement(s);
  }

  @Override
  public CallableStatement prepareCall(String s) throws SQLException {
    return connection.prepareCall(s);
  }

  @Override
  public String nativeSQL(String s) throws SQLException {
    return connection.nativeSQL(s);
  }

  @Override
  public void setAutoCommit(boolean b) throws SQLException {
    connection.setAutoCommit(b);
  }

  @Override
  public boolean getAutoCommit() throws SQLException {
    return connection.getAutoCommit();
  }

  @Override
  public void commit() throws SQLException {
    connection.commit();
  }

  @Override
  public void rollback() throws SQLException {
    connection.rollback();
  }

  @Override
  public void close() throws SQLException {
    connection.close();
  }

  @Override
  public boolean isClosed() throws SQLException {
    return connection.isClosed();
  }

  @Override
  public DatabaseMetaData getMetaData() throws SQLException {
    return connection.getMetaData();
  }

  @Override
  public void setReadOnly(boolean b) throws SQLException {
    connection.setReadOnly(b);
  }

  @Override
  public boolean isReadOnly() throws SQLException {
    return connection.isReadOnly();
  }

  @Override
  public void setCatalog(String s) throws SQLException {
    connection.setCatalog(s);
  }

  @Override
  public String getCatalog() throws SQLException {
    return connection.getCatalog();
  }

  @Override
  public void setTransactionIsolation(int i) throws SQLException {
    connection.setTransactionIsolation(i);
  }

  @Override
  public int getTransactionIsolation() throws SQLException {
    return connection.getTransactionIsolation();
  }

  @Override
  public SQLWarning getWarnings() throws SQLException {
    return connection.getWarnings();
  }

  @Override
  public void clearWarnings() throws SQLException {
    connection.clearWarnings();
  }

  @Override
  public Statement createStatement(int i, int i1) throws SQLException {
    return connection.createStatement(i, i1);
  }

  @Override
  public PreparedStatement prepareStatement(String s, int i, int i1) throws SQLException {
    throw new UnsupportedOperationException();
//    return connection.prepareStatement(s, i, i1);
  }

  @Override
  public CallableStatement prepareCall(String s, int i, int i1) throws SQLException {
    return connection.prepareCall(s, i, i1);
  }

  @Override
  public Map<String, Class<?>> getTypeMap() throws SQLException {
    return connection.getTypeMap();
  }

  @Override
  public void setTypeMap(Map<String, Class<?>> map) throws SQLException {
    connection.setTypeMap(map);
  }

  @Override
  public void setHoldability(int i) throws SQLException {
    connection.setHoldability(i);
  }

  @Override
  public int getHoldability() throws SQLException {
    return connection.getHoldability();
  }

  @Override
  public Savepoint setSavepoint() throws SQLException {
    return connection.setSavepoint();
  }

  @Override
  public Savepoint setSavepoint(String s) throws SQLException {
    return connection.setSavepoint(s);
  }

  @Override
  public void rollback(Savepoint savepoint) throws SQLException {
    connection.rollback(savepoint);
  }

  @Override
  public void releaseSavepoint(Savepoint savepoint) throws SQLException {
    connection.releaseSavepoint(savepoint);
  }

  @Override
  public Statement createStatement(int i, int i1, int i2) throws SQLException {
    return connection.createStatement(i, i1, i2);
  }

  @Override
  public PreparedStatement prepareStatement(String s, int i, int i1, int i2) throws SQLException {
    throw new UnsupportedOperationException();
//    return connection.prepareStatement(s, i, i1, i2);
  }

  @Override
  public CallableStatement prepareCall(String s, int i, int i1, int i2) throws SQLException {
    throw new UnsupportedOperationException();
//    return connection.prepareCall(s, i, i1, i2);
  }

  @Override
  public PreparedStatement prepareStatement(String s, int i) throws SQLException {
    throw new UnsupportedOperationException();
//    return connection.prepareStatement(s, i);
  }

  @Override
  public PreparedStatement prepareStatement(String s, int[] ints) throws SQLException {
    throw new UnsupportedOperationException();
//    return connection.prepareStatement(s, ints);
  }

  @Override
  public PreparedStatement prepareStatement(String s, String[] strings) throws SQLException {
    throw new UnsupportedOperationException();
//    return connection.prepareStatement(s, strings);
  }

  @Override
  public Clob createClob() throws SQLException {
    return connection.createClob();
  }

  @Override
  public Blob createBlob() throws SQLException {
    return connection.createBlob();
  }

  @Override
  public NClob createNClob() throws SQLException {
    return connection.createNClob();
  }

  @Override
  public SQLXML createSQLXML() throws SQLException {
    return connection.createSQLXML();
  }

  @Override
  public boolean isValid(int i) throws SQLException {
    return connection.isValid(i);
  }

  @Override
  public void setClientInfo(String s, String s1) throws SQLClientInfoException {
    connection.setClientInfo(s, s1);
  }

  @Override
  public void setClientInfo(Properties properties) throws SQLClientInfoException {
    connection.setClientInfo(properties);
  }

  @Override
  public String getClientInfo(String s) throws SQLException {
    return connection.getClientInfo(s);
  }

  @Override
  public Properties getClientInfo() throws SQLException {
    return connection.getClientInfo();
  }

  @Override
  public Array createArrayOf(String s, Object[] objects) throws SQLException {
    return connection.createArrayOf(s, objects);
  }

  @Override
  public Struct createStruct(String s, Object[] objects) throws SQLException {
    return connection.createStruct(s, objects);
  }

  @Override
  public void setSchema(String s) throws SQLException {
    connection.setSchema(s);
  }

  @Override
  public String getSchema() throws SQLException {
    return connection.getSchema();
  }

  @Override
  public void abort(Executor executor) throws SQLException {
    connection.abort(executor);
  }

  @Override
  public void setNetworkTimeout(Executor executor, int i) throws SQLException {
    connection.setNetworkTimeout(executor, i);
  }

  @Override
  public int getNetworkTimeout() throws SQLException {
    return connection.getNetworkTimeout();
  }

  @Override
  public <T> T unwrap(Class<T> aClass) throws SQLException {
    return connection.unwrap(aClass);
  }

  @Override
  public boolean isWrapperFor(Class<?> aClass) throws SQLException {
    return connection.isWrapperFor(aClass);
  }

  private class UnpreparedStatement implements PreparedStatement {
    private Statement statement;
    private String query;
    private String[] values;

    private UnpreparedStatement(String query) throws SQLException {
      this.query = query;
      this.values= new String[query.split("\\?").length - 1];
      statement = connection.createStatement();
    }

    private String prepare() {
      StringBuilder preparedQuery = new StringBuilder();
      String q = query;
      for (String value : values) {
        int i = q.indexOf("?");
        preparedQuery.append(q.substring(0, i));
        preparedQuery.append(value == null ? "null" : value);
        q = q.substring(i + 1);
      }
      preparedQuery.append(q);
      return preparedQuery.toString();
    }

    @Override
    public ResultSet executeQuery() throws SQLException {
      return executeQuery(prepare());
    }

    @Override
    public int executeUpdate() throws SQLException {
      return executeUpdate(prepare());
    }

    @Override
    public void setNull(int i, int i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setBoolean(int i, boolean b) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setByte(int i, byte b) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setShort(int i, short i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setInt(int i, int i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setLong(int i, long l) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setFloat(int i, float v) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setDouble(int i, double v) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setBigDecimal(int i, BigDecimal bigDecimal) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setString(int i, String s) throws SQLException {
      // not really properly escaped but oh well
      values[i - 1] = "'" + s.replace("'", "''") + "'";
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
    public void setUnicodeStream(int i, InputStream inputStream, int i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setBinaryStream(int i, InputStream inputStream, int i1) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void clearParameters() throws SQLException {
      throw new UnsupportedOperationException();
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
      return execute(prepare());
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
      throw new UnsupportedOperationException();
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
      throw new UnsupportedOperationException();
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
      return executeLargeUpdate(prepare());
    }

    @Override
    public ResultSet executeQuery(String s) throws SQLException {
      return statement.executeQuery(s);
    }

    @Override
    public int executeUpdate(String s) throws SQLException {
      return statement.executeUpdate(s);
    }

    @Override
    public void close() throws SQLException {
      statement.close();
    }

    @Override
    public int getMaxFieldSize() throws SQLException {
      return statement.getMaxFieldSize();
    }

    @Override
    public void setMaxFieldSize(int i) throws SQLException {
      statement.setMaxFieldSize(i);
    }

    @Override
    public int getMaxRows() throws SQLException {
      return statement.getMaxRows();
    }

    @Override
    public void setMaxRows(int i) throws SQLException {
      statement.setMaxRows(i);
    }

    @Override
    public void setEscapeProcessing(boolean b) throws SQLException {
      statement.setEscapeProcessing(b);
    }

    @Override
    public int getQueryTimeout() throws SQLException {
      return statement.getQueryTimeout();
    }

    @Override
    public void setQueryTimeout(int i) throws SQLException {
      statement.setQueryTimeout(i);
    }

    @Override
    public void cancel() throws SQLException {
      statement.cancel();
    }

    @Override
    public SQLWarning getWarnings() throws SQLException {
      return statement.getWarnings();
    }

    @Override
    public void clearWarnings() throws SQLException {
      statement.clearWarnings();
    }

    @Override
    public void setCursorName(String s) throws SQLException {
      statement.setCursorName(s);
    }

    @Override
    public boolean execute(String s) throws SQLException {
      return statement.execute(s);
    }

    @Override
    public ResultSet getResultSet() throws SQLException {
      return statement.getResultSet();
    }

    @Override
    public int getUpdateCount() throws SQLException {
      return statement.getUpdateCount();
    }

    @Override
    public boolean getMoreResults() throws SQLException {
      return statement.getMoreResults();
    }

    @Override
    public void setFetchDirection(int i) throws SQLException {
      statement.setFetchDirection(i);
    }

    @Override
    public int getFetchDirection() throws SQLException {
      return statement.getFetchDirection();
    }

    @Override
    public void setFetchSize(int i) throws SQLException {
      statement.setFetchSize(i);
    }

    @Override
    public int getFetchSize() throws SQLException {
      return statement.getFetchSize();
    }

    @Override
    public int getResultSetConcurrency() throws SQLException {
      return statement.getResultSetConcurrency();
    }

    @Override
    public int getResultSetType() throws SQLException {
      return statement.getResultSetType();
    }

    @Override
    public void addBatch(String s) throws SQLException {
      statement.addBatch(s);
    }

    @Override
    public void clearBatch() throws SQLException {
      statement.clearBatch();
    }

    @Override
    public int[] executeBatch() throws SQLException {
      return statement.executeBatch();
    }

    @Override
    public Connection getConnection() throws SQLException {
      return statement.getConnection();
    }

    @Override
    public boolean getMoreResults(int i) throws SQLException {
      return statement.getMoreResults(i);
    }

    @Override
    public ResultSet getGeneratedKeys() throws SQLException {
      return statement.getGeneratedKeys();
    }

    @Override
    public int executeUpdate(String s, int i) throws SQLException {
      return statement.executeUpdate(s, i);
    }

    @Override
    public int executeUpdate(String s, int[] ints) throws SQLException {
      return statement.executeUpdate(s, ints);
    }

    @Override
    public int executeUpdate(String s, String[] strings) throws SQLException {
      return statement.executeUpdate(s, strings);
    }

    @Override
    public boolean execute(String s, int i) throws SQLException {
      return statement.execute(s, i);
    }

    @Override
    public boolean execute(String s, int[] ints) throws SQLException {
      return statement.execute(s, ints);
    }

    @Override
    public boolean execute(String s, String[] strings) throws SQLException {
      return statement.execute(s, strings);
    }

    @Override
    public int getResultSetHoldability() throws SQLException {
      return statement.getResultSetHoldability();
    }

    @Override
    public boolean isClosed() throws SQLException {
      return statement.isClosed();
    }

    @Override
    public void setPoolable(boolean b) throws SQLException {
      statement.setPoolable(b);
    }

    @Override
    public boolean isPoolable() throws SQLException {
      return statement.isPoolable();
    }

    @Override
    public void closeOnCompletion() throws SQLException {
      statement.closeOnCompletion();
    }

    @Override
    public boolean isCloseOnCompletion() throws SQLException {
      return statement.isCloseOnCompletion();
    }

    @Override
    public long getLargeUpdateCount() throws SQLException {
      return statement.getLargeUpdateCount();
    }

    @Override
    public void setLargeMaxRows(long l) throws SQLException {
      statement.setLargeMaxRows(l);
    }

    @Override
    public long getLargeMaxRows() throws SQLException {
      return statement.getLargeMaxRows();
    }

    @Override
    public long[] executeLargeBatch() throws SQLException {
      return statement.executeLargeBatch();
    }

    @Override
    public long executeLargeUpdate(String s) throws SQLException {
      return statement.executeLargeUpdate(s);
    }

    @Override
    public long executeLargeUpdate(String s, int i) throws SQLException {
      return statement.executeLargeUpdate(s, i);
    }

    @Override
    public long executeLargeUpdate(String s, int[] ints) throws SQLException {
      return statement.executeLargeUpdate(s, ints);
    }

    @Override
    public long executeLargeUpdate(String s, String[] strings) throws SQLException {
      return statement.executeLargeUpdate(s, strings);
    }

    @Override
    public <T> T unwrap(Class<T> aClass) throws SQLException {
      return statement.unwrap(aClass);
    }

    @Override
    public boolean isWrapperFor(Class<?> aClass) throws SQLException {
      return statement.isWrapperFor(aClass);
    }
  }
}
