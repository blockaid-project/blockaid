package jdbc;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import fatjdbc.PlanExecutor;
import org.apache.calcite.avatica.AvaticaSqlException;
import org.apache.calcite.avatica.Meta;
import org.apache.calcite.sql.SqlKind;
import sql.*;

import java.io.InputStream;
import java.io.Reader;
import java.math.BigDecimal;
import java.net.URL;
import java.sql.*;
import java.util.Calendar;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executor;
import java.util.concurrent.TimeUnit;

class PrivacyConnection implements Connection {
  private Connection proxy_connection;
  private Connection direct_connection;
//  private HashMap<Policy, LoadingCache<PrivacyQuery ,Boolean>> policy_decision_cache;
  private LoadingCache<PrivacyQuery, Boolean> policy_decision_cache;
  private Parser parser;

  PrivacyConnection(Connection proxy_connection, Connection direct_connection, Properties direct_info) throws SQLException {
    this.proxy_connection = proxy_connection;
    this.direct_connection = direct_connection;
    this.policy_decision_cache = CacheBuilder.newBuilder()
        .expireAfterAccess(100000, TimeUnit.SECONDS)
        .maximumSize(50)
        .build(new CacheLoader<PrivacyQuery, Boolean>() {
          @Override
          public Boolean load(final PrivacyQuery query) throws Exception {
            // todo?
            return false;
          }
        });
    Properties info = direct_info;
    info.setProperty("schemaFactory", "catalog.db.SchemaFactory");
    this.parser = new ParserFactory(info).getParser(info);
  }

  private boolean checkQueryCompliance(PrivacyQuery query){
      try{
          // TODO maybe change from "direct if in cache and true, proxy otherwise"?
          boolean decision = policy_decision_cache.get(query);
          System.out.println(query + ": " + decision);
          return decision;
      } catch (ExecutionException e){
          throw propagate(e);
      }
  }

  private void setQueryCompliance(PrivacyQuery query, boolean compliance) {
      this.policy_decision_cache.put(query, compliance);
    System.out.println(query + " = " + compliance);
  }

  private boolean shouldApplyPolicy(SqlKind kind)
  {
    if (kind.equals(kind.SELECT)){
      return true;
    }
    else
      return false;
  }

  private RuntimeException propagate(Throwable e) {
      if (e instanceof RuntimeException) {
          throw (RuntimeException) e;
      } else if (e instanceof Error) {
          throw (Error) e;
      } else {
          throw new RuntimeException(e.getMessage());
      }
  }

  @Override
  public Statement createStatement() throws SQLException {
    return new PrivacyStatement();
  }

  @Override
  public PreparedStatement prepareStatement(String s) throws SQLException {
    return new PrivacyPreparedStatement(s);
  }

  @Override
  public CallableStatement prepareCall(String s) throws SQLException {
    return proxy_connection.prepareCall(s);
  }

  @Override
  public String nativeSQL(String s) throws SQLException {
    return proxy_connection.nativeSQL(s);
  }

  @Override
  public void setAutoCommit(boolean b) throws SQLException {
    proxy_connection.setAutoCommit(b);
  }

  @Override
  public boolean getAutoCommit() throws SQLException {
    return proxy_connection.getAutoCommit();
  }

  @Override
  public void commit() throws SQLException {
    proxy_connection.commit();
  }

  @Override
  public void rollback() throws SQLException {
    proxy_connection.rollback();
  }

  @Override
  public void close() throws SQLException {
    proxy_connection.close();
    direct_connection.close();
  }

  @Override
  public boolean isClosed() throws SQLException {
    return proxy_connection.isClosed();
  }

  @Override
  public DatabaseMetaData getMetaData() throws SQLException {
    return proxy_connection.getMetaData();
  }

  @Override
  public void setReadOnly(boolean b) throws SQLException {
    proxy_connection.setReadOnly(b);
  }

  @Override
  public boolean isReadOnly() throws SQLException {
    return proxy_connection.isReadOnly();
  }

  @Override
  public void setCatalog(String s) throws SQLException {
    proxy_connection.setCatalog(s);
  }

  @Override
  public String getCatalog() throws SQLException {
    return proxy_connection.getCatalog();
  }

  @Override
  public void setTransactionIsolation(int i) throws SQLException {
    proxy_connection.setTransactionIsolation(i);
  }

  @Override
  public int getTransactionIsolation() throws SQLException {
    return proxy_connection.getTransactionIsolation();
  }

  @Override
  public SQLWarning getWarnings() throws SQLException {
    return proxy_connection.getWarnings();
  }

  @Override
  public void clearWarnings() throws SQLException {
    proxy_connection.clearWarnings();
  }

  @Override
  public Statement createStatement(int i, int i1) throws SQLException {
    throw new UnsupportedOperationException();
  }

  @Override
  public PreparedStatement prepareStatement(String s, int i, int i1) throws SQLException {
    return proxy_connection.prepareStatement(s, i, i1);
  }

  @Override
  public CallableStatement prepareCall(String s, int i, int i1) throws SQLException {
    return proxy_connection.prepareCall(s, i, i1);
  }

  @Override
  public Map<String, Class<?>> getTypeMap() throws SQLException {
    return proxy_connection.getTypeMap();
  }

  @Override
  public void setTypeMap(Map<String, Class<?>> map) throws SQLException {
    proxy_connection.setTypeMap(map);
  }

  @Override
  public void setHoldability(int i) throws SQLException {
    proxy_connection.setHoldability(i);
  }

  @Override
  public int getHoldability() throws SQLException {
    return proxy_connection.getHoldability();
  }

  @Override
  public Savepoint setSavepoint() throws SQLException {
    return proxy_connection.setSavepoint();
  }

  @Override
  public Savepoint setSavepoint(String s) throws SQLException {
    return proxy_connection.setSavepoint(s);
  }

  @Override
  public void rollback(Savepoint savepoint) throws SQLException {
    proxy_connection.rollback(savepoint);
  }

  @Override
  public void releaseSavepoint(Savepoint savepoint) throws SQLException {
    proxy_connection.releaseSavepoint(savepoint);
  }

  @Override
  public Statement createStatement(int i, int i1, int i2) throws SQLException {
    throw new UnsupportedOperationException();
  }

  @Override
  public PreparedStatement prepareStatement(String s, int i, int i1, int i2) throws SQLException {
    return proxy_connection.prepareStatement(s, i, i1, i2);
  }

  @Override
  public CallableStatement prepareCall(String s, int i, int i1, int i2) throws SQLException {
    return proxy_connection.prepareCall(s, i, i1, i2);
  }

  @Override
  public PreparedStatement prepareStatement(String s, int i) throws SQLException {
    return proxy_connection.prepareStatement(s, i);
  }

  @Override
  public PreparedStatement prepareStatement(String s, int[] ints) throws SQLException {
    return proxy_connection.prepareStatement(s, ints);
  }

  @Override
  public PreparedStatement prepareStatement(String s, String[] strings) throws SQLException {
    return proxy_connection.prepareStatement(s, strings);
  }

  @Override
  public Clob createClob() throws SQLException {
    return proxy_connection.createClob();
  }

  @Override
  public Blob createBlob() throws SQLException {
    return proxy_connection.createBlob();
  }

  @Override
  public NClob createNClob() throws SQLException {
    return proxy_connection.createNClob();
  }

  @Override
  public SQLXML createSQLXML() throws SQLException {
    return proxy_connection.createSQLXML();
  }

  @Override
  public boolean isValid(int i) throws SQLException {
    return proxy_connection.isValid(i);
  }

  @Override
  public void setClientInfo(String s, String s1) throws SQLClientInfoException {
    proxy_connection.setClientInfo(s, s1);
  }

  @Override
  public void setClientInfo(Properties properties) throws SQLClientInfoException {
    proxy_connection.setClientInfo(properties);
  }

  @Override
  public String getClientInfo(String s) throws SQLException {
    return proxy_connection.getClientInfo(s);
  }

  @Override
  public Properties getClientInfo() throws SQLException {
    return proxy_connection.getClientInfo();
  }

  @Override
  public Array createArrayOf(String s, Object[] objects) throws SQLException {
    return proxy_connection.createArrayOf(s, objects);
  }

  @Override
  public Struct createStruct(String s, Object[] objects) throws SQLException {
    return proxy_connection.createStruct(s, objects);
  }

  @Override
  public void setSchema(String s) throws SQLException {
    proxy_connection.setSchema(s);
  }

  @Override
  public String getSchema() throws SQLException {
    return proxy_connection.getSchema();
  }

  @Override
  public void abort(Executor executor) throws SQLException {
    proxy_connection.abort(executor);
  }

  @Override
  public void setNetworkTimeout(Executor executor, int i) throws SQLException {
    proxy_connection.setNetworkTimeout(executor, i);
  }

  @Override
  public int getNetworkTimeout() throws SQLException {
    return proxy_connection.getNetworkTimeout();
  }

  @Override
  public <T> T unwrap(Class<T> aClass) throws SQLException {
    return proxy_connection.unwrap(aClass);
  }

  @Override
  public boolean isWrapperFor(Class<?> aClass) throws SQLException {
    return proxy_connection.isWrapperFor(aClass);
  }

  private class PrivacyPreparedStatement implements PreparedStatement {
    private PreparedStatement proxy_statement;
    private PreparedStatement direct_statement;
    private String query;
    private String[] values;

    PrivacyPreparedStatement(String sql) throws SQLException {
      query = sql;
      values = new String[sql.split("\\?").length];

      if (shouldApplyPolicy(parser.parse(sql).getSqlNode().getKind())) {
        // big hack
        String direct_sql = sql.replace("canonical.", "");
        proxy_statement = proxy_connection.prepareStatement(sql);
        direct_statement = direct_connection.prepareStatement(direct_sql);
      } else {
        proxy_statement = null;
        direct_statement = direct_connection.prepareStatement(sql);
      }
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
      PreparedStatement active_statement = direct_statement;
      PrivacyQuery privacy_query = null;
      if (proxy_statement != null) {
        ParserResult parser_result = parser.parse(prepare());
        privacy_query = PrivacyQueryFactory.createPrivacyQuery(parser_result);
        if (shouldApplyPolicy(parser_result.getSqlNode().getKind())) {
          if (checkQueryCompliance(privacy_query)) {
            active_statement = direct_statement;
          } else {
            active_statement = proxy_statement;
          }
        }
      }

      try {
        ResultSet set = active_statement.executeQuery();
        if (privacy_query != null) {
          setQueryCompliance(privacy_query, true);
        }
        return set;
      } catch (AvaticaSqlException e) {
        if (e.getMessage().contains("Privacy compliance was not met") && privacy_query != null) {
          setQueryCompliance(privacy_query, false);
        }
        throw e;
      }
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
      if (proxy_statement != null) {
        proxy_statement.setBoolean(i, b);
      }
      direct_statement.setBoolean(i, b);
      values[i - 1] = Boolean.toString(b);
    }

    @Override
    public void setByte(int i, byte b) throws SQLException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void setShort(int i, short i1) throws SQLException {
      if (proxy_statement != null) {
        proxy_statement.setShort(i, i1);
      }
      direct_statement.setShort(i, i1);
    }

    @Override
    public void setInt(int i, int i1) throws SQLException {
      if (proxy_statement != null) {
        proxy_statement.setInt(i, i1);
      }
      direct_statement.setInt(i, i1);
      values[i - 1] = Integer.toString(i1);
    }

    @Override
    public void setLong(int i, long l) throws SQLException {
      if (proxy_statement != null) {
        proxy_statement.setLong(i, l);
      }
      direct_statement.setLong(i, l);
      values[i - 1] = Long.toString(l);
    }

    @Override
    public void setFloat(int i, float v) throws SQLException {
      if (proxy_statement != null) {
        proxy_statement.setFloat(i, v);
      }
      direct_statement.setFloat(i, v);
      values[i - 1] = Float.toString(v);
    }

    @Override
    public void setDouble(int i, double v) throws SQLException {
      if (proxy_statement != null) {
        proxy_statement.setDouble(i, v);
      }
      direct_statement.setDouble(i, v);
      values[i - 1] = Double.toString(v);
    }

    @Override
    public void setBigDecimal(int i, BigDecimal bigDecimal) throws SQLException {
      if (proxy_statement != null) {
        proxy_statement.setBigDecimal(i, bigDecimal);
      }
      direct_statement.setBigDecimal(i, bigDecimal);
      values[i - 1] = bigDecimal.toString();
    }

    @Override
    public void setString(int i, String s) throws SQLException {
      if (proxy_statement != null) {
        proxy_statement.setString(i, s);
      }
      direct_statement.setString(i, s);
      // not really properly escaped todo fix
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
      proxy_statement.clearParameters();
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
      proxy_statement.close();
      direct_statement.close();
    }

    @Override
    public int getMaxFieldSize() throws SQLException {
      return direct_statement.getMaxFieldSize();
    }

    @Override
    public void setMaxFieldSize(int i) throws SQLException {
      proxy_statement.setMaxFieldSize(i);
      direct_statement.setMaxFieldSize(i);
    }

    @Override
    public int getMaxRows() throws SQLException {
      return direct_statement.getMaxRows();
    }

    @Override
    public void setMaxRows(int i) throws SQLException {
      proxy_statement.setMaxRows(i);
      direct_statement.setMaxRows(i);
    }

    @Override
    public void setEscapeProcessing(boolean b) throws SQLException {
      proxy_statement.setEscapeProcessing(b);
      direct_statement.setEscapeProcessing(b);
    }

    @Override
    public int getQueryTimeout() throws SQLException {
      return direct_statement.getQueryTimeout();
    }

    @Override
    public void setQueryTimeout(int i) throws SQLException {
      proxy_statement.setQueryTimeout(i);
      direct_statement.setQueryTimeout(i);
    }

    @Override
    public void cancel() throws SQLException {
      proxy_statement.cancel();
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
    private Statement proxy_statement;
    private Statement direct_statement;
    private Statement active_statment;

    private PrivacyStatement() throws SQLException {
      this.proxy_statement = proxy_connection.createStatement();
      this.direct_statement = direct_connection.createStatement();

      // TODO
      this.active_statment = this.proxy_statement;
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
