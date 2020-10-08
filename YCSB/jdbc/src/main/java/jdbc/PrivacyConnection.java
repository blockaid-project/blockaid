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
            // todo
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
          return policy_decision_cache.get(query);
      } catch (ExecutionException e){
          throw propagate(e);
      }
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
    private PreparedStatement active_statement;
    private ParserResult parser_result;

    PrivacyPreparedStatement(String sql) throws SQLException {
      // todo parameters?
      this.parser_result = parser.parse(sql);
      // big hack
      String direct_sql = sql.replace("canonical.", "");
      System.out.println(sql);
      System.out.println(direct_sql);
      System.out.println("foo");
      if (!sql.contains("SELECT")) {
        proxy_statement = null;
        direct_statement = direct_connection.prepareStatement(direct_sql);
        active_statement = direct_statement;
      } else {
        proxy_statement = proxy_connection.prepareStatement(sql);
        direct_statement = direct_connection.prepareStatement(direct_sql);
        active_statement = proxy_statement;
      }
    }

    @Override
    public ResultSet executeQuery() throws SQLException {
      boolean allowed = true;

      if (shouldApplyPolicy(parser_result.getSqlNode().getKind())) {
        if (checkQueryCompliance(PrivacyQueryFactory.createPrivacyQuery(parser_result))) {
          active_statement = direct_statement;
        } else {
          active_statement = proxy_statement;
        }
      }

      try {
        return active_statement.executeQuery();
      } catch (AvaticaSqlException e) {
        if (e.getMessage().contains("Privacy compliance was not met")) {
          allowed = false;
        }
        throw e;
      } finally {
        System.out.println("compliance: " + allowed); // todo
      }
    }

    @Override
    public int executeUpdate() throws SQLException {
      return active_statement.executeUpdate();
    }

    @Override
    public void setNull(int i, int i1) throws SQLException {
      active_statement.setNull(i, i1);
    }

    @Override
    public void setBoolean(int i, boolean b) throws SQLException {
      active_statement.setBoolean(i, b);
    }

    @Override
    public void setByte(int i, byte b) throws SQLException {
      active_statement.setByte(i, b);
    }

    @Override
    public void setShort(int i, short i1) throws SQLException {
      active_statement.setShort(i, i1);
    }

    @Override
    public void setInt(int i, int i1) throws SQLException {
      active_statement.setInt(i, i1);
    }

    @Override
    public void setLong(int i, long l) throws SQLException {
      active_statement.setLong(i, l);
    }

    @Override
    public void setFloat(int i, float v) throws SQLException {
      active_statement.setFloat(i, v);
    }

    @Override
    public void setDouble(int i, double v) throws SQLException {
      active_statement.setDouble(i, v);
    }

    @Override
    public void setBigDecimal(int i, BigDecimal bigDecimal) throws SQLException {
      active_statement.setBigDecimal(i, bigDecimal);
    }

    @Override
    public void setString(int i, String s) throws SQLException {
      active_statement.setString(i, s);
    }

    @Override
    public void setBytes(int i, byte[] bytes) throws SQLException {
      active_statement.setBytes(i, bytes);
    }

    @Override
    public void setDate(int i, Date date) throws SQLException {
      active_statement.setDate(i, date);
    }

    @Override
    public void setTime(int i, Time time) throws SQLException {
      active_statement.setTime(i, time);
    }

    @Override
    public void setTimestamp(int i, Timestamp timestamp) throws SQLException {
      active_statement.setTimestamp(i, timestamp);
    }

    @Override
    public void setAsciiStream(int i, InputStream inputStream, int i1) throws SQLException {
      active_statement.setAsciiStream(i, inputStream, i1);
    }

    @Override
    @Deprecated
    public void setUnicodeStream(int i, InputStream inputStream, int i1) throws SQLException {
      active_statement.setUnicodeStream(i, inputStream, i1);
    }

    @Override
    public void setBinaryStream(int i, InputStream inputStream, int i1) throws SQLException {
      active_statement.setBinaryStream(i, inputStream, i1);
    }

    @Override
    public void clearParameters() throws SQLException {
      active_statement.clearParameters();
    }

    @Override
    public void setObject(int i, Object o, int i1) throws SQLException {
      active_statement.setObject(i, o, i1);
    }

    @Override
    public void setObject(int i, Object o) throws SQLException {
      active_statement.setObject(i, o);
    }

    @Override
    public boolean execute() throws SQLException {
      return active_statement.execute();
    }

    @Override
    public void addBatch() throws SQLException {
      active_statement.addBatch();
    }

    @Override
    public void setCharacterStream(int i, Reader reader, int i1) throws SQLException {
      active_statement.setCharacterStream(i, reader, i1);
    }

    @Override
    public void setRef(int i, Ref ref) throws SQLException {
      active_statement.setRef(i, ref);
    }

    @Override
    public void setBlob(int i, Blob blob) throws SQLException {
      active_statement.setBlob(i, blob);
    }

    @Override
    public void setClob(int i, Clob clob) throws SQLException {
      active_statement.setClob(i, clob);
    }

    @Override
    public void setArray(int i, Array array) throws SQLException {
      active_statement.setArray(i, array);
    }

    @Override
    public ResultSetMetaData getMetaData() throws SQLException {
      return active_statement.getMetaData();
    }

    @Override
    public void setDate(int i, Date date, Calendar calendar) throws SQLException {
      active_statement.setDate(i, date, calendar);
    }

    @Override
    public void setTime(int i, Time time, Calendar calendar) throws SQLException {
      active_statement.setTime(i, time, calendar);
    }

    @Override
    public void setTimestamp(int i, Timestamp timestamp, Calendar calendar) throws SQLException {
      active_statement.setTimestamp(i, timestamp, calendar);
    }

    @Override
    public void setNull(int i, int i1, String s) throws SQLException {
      active_statement.setNull(i, i1, s);
    }

    @Override
    public void setURL(int i, URL url) throws SQLException {
      active_statement.setURL(i, url);
    }

    @Override
    public ParameterMetaData getParameterMetaData() throws SQLException {
      return active_statement.getParameterMetaData();
    }

    @Override
    public void setRowId(int i, RowId rowId) throws SQLException {
      active_statement.setRowId(i, rowId);
    }

    @Override
    public void setNString(int i, String s) throws SQLException {
      active_statement.setNString(i, s);
    }

    @Override
    public void setNCharacterStream(int i, Reader reader, long l) throws SQLException {
      active_statement.setNCharacterStream(i, reader, l);
    }

    @Override
    public void setNClob(int i, NClob nClob) throws SQLException {
      active_statement.setNClob(i, nClob);
    }

    @Override
    public void setClob(int i, Reader reader, long l) throws SQLException {
      active_statement.setClob(i, reader, l);
    }

    @Override
    public void setBlob(int i, InputStream inputStream, long l) throws SQLException {
      active_statement.setBlob(i, inputStream, l);
    }

    @Override
    public void setNClob(int i, Reader reader, long l) throws SQLException {
      active_statement.setNClob(i, reader, l);
    }

    @Override
    public void setSQLXML(int i, SQLXML sqlxml) throws SQLException {
      active_statement.setSQLXML(i, sqlxml);
    }

    @Override
    public void setObject(int i, Object o, int i1, int i2) throws SQLException {
      active_statement.setObject(i, o, i1, i2);
    }

    @Override
    public void setAsciiStream(int i, InputStream inputStream, long l) throws SQLException {
      active_statement.setAsciiStream(i, inputStream, l);
    }

    @Override
    public void setBinaryStream(int i, InputStream inputStream, long l) throws SQLException {
      active_statement.setBinaryStream(i, inputStream, l);
    }

    @Override
    public void setCharacterStream(int i, Reader reader, long l) throws SQLException {
      active_statement.setCharacterStream(i, reader, l);
    }

    @Override
    public void setAsciiStream(int i, InputStream inputStream) throws SQLException {
      active_statement.setAsciiStream(i, inputStream);
    }

    @Override
    public void setBinaryStream(int i, InputStream inputStream) throws SQLException {
      active_statement.setBinaryStream(i, inputStream);
    }

    @Override
    public void setCharacterStream(int i, Reader reader) throws SQLException {
      active_statement.setCharacterStream(i, reader);
    }

    @Override
    public void setNCharacterStream(int i, Reader reader) throws SQLException {
      active_statement.setNCharacterStream(i, reader);
    }

    @Override
    public void setClob(int i, Reader reader) throws SQLException {
      active_statement.setClob(i, reader);
    }

    @Override
    public void setBlob(int i, InputStream inputStream) throws SQLException {
      active_statement.setBlob(i, inputStream);
    }

    @Override
    public void setNClob(int i, Reader reader) throws SQLException {
      active_statement.setNClob(i, reader);
    }

    @Override
    public void setObject(int i, Object o, SQLType sqlType, int i1) throws SQLException {
      active_statement.setObject(i, o, sqlType, i1);
    }

    @Override
    public void setObject(int i, Object o, SQLType sqlType) throws SQLException {
      active_statement.setObject(i, o, sqlType);
    }

    @Override
    public long executeLargeUpdate() throws SQLException {
      return active_statement.executeLargeUpdate();
    }

    @Override
    public ResultSet executeQuery(String s) throws SQLException {
      return active_statement.executeQuery(s);
    }

    @Override
    public int executeUpdate(String s) throws SQLException {
      return active_statement.executeUpdate(s);
    }

    @Override
    public void close() throws SQLException {
      active_statement.close();
    }

    @Override
    public int getMaxFieldSize() throws SQLException {
      return active_statement.getMaxFieldSize();
    }

    @Override
    public void setMaxFieldSize(int i) throws SQLException {
      active_statement.setMaxFieldSize(i);
    }

    @Override
    public int getMaxRows() throws SQLException {
      return active_statement.getMaxRows();
    }

    @Override
    public void setMaxRows(int i) throws SQLException {
      active_statement.setMaxRows(i);
    }

    @Override
    public void setEscapeProcessing(boolean b) throws SQLException {
      active_statement.setEscapeProcessing(b);
    }

    @Override
    public int getQueryTimeout() throws SQLException {
      return active_statement.getQueryTimeout();
    }

    @Override
    public void setQueryTimeout(int i) throws SQLException {
      active_statement.setQueryTimeout(i);
    }

    @Override
    public void cancel() throws SQLException {
      active_statement.cancel();
    }

    @Override
    public SQLWarning getWarnings() throws SQLException {
      return active_statement.getWarnings();
    }

    @Override
    public void clearWarnings() throws SQLException {
      active_statement.clearWarnings();
    }

    @Override
    public void setCursorName(String s) throws SQLException {
      active_statement.setCursorName(s);
    }

    @Override
    public boolean execute(String s) throws SQLException {
      return active_statement.execute(s);
    }

    @Override
    public ResultSet getResultSet() throws SQLException {
      return active_statement.getResultSet();
    }

    @Override
    public int getUpdateCount() throws SQLException {
      return active_statement.getUpdateCount();
    }

    @Override
    public boolean getMoreResults() throws SQLException {
      return active_statement.getMoreResults();
    }

    @Override
    public void setFetchDirection(int i) throws SQLException {
      active_statement.setFetchDirection(i);
    }

    @Override
    public int getFetchDirection() throws SQLException {
      return active_statement.getFetchDirection();
    }

    @Override
    public void setFetchSize(int i) throws SQLException {
      active_statement.setFetchSize(i);
    }

    @Override
    public int getFetchSize() throws SQLException {
      return active_statement.getFetchSize();
    }

    @Override
    public int getResultSetConcurrency() throws SQLException {
      return active_statement.getResultSetConcurrency();
    }

    @Override
    public int getResultSetType() throws SQLException {
      return active_statement.getResultSetType();
    }

    @Override
    public void addBatch(String s) throws SQLException {
      active_statement.addBatch(s);
    }

    @Override
    public void clearBatch() throws SQLException {
      active_statement.clearBatch();
    }

    @Override
    public int[] executeBatch() throws SQLException {
      return active_statement.executeBatch();
    }

    @Override
    public Connection getConnection() throws SQLException {
      return active_statement.getConnection();
    }

    @Override
    public boolean getMoreResults(int i) throws SQLException {
      return active_statement.getMoreResults(i);
    }

    @Override
    public ResultSet getGeneratedKeys() throws SQLException {
      return active_statement.getGeneratedKeys();
    }

    @Override
    public int executeUpdate(String s, int i) throws SQLException {
      return active_statement.executeUpdate(s, i);
    }

    @Override
    public int executeUpdate(String s, int[] ints) throws SQLException {
      return active_statement.executeUpdate(s, ints);
    }

    @Override
    public int executeUpdate(String s, String[] strings) throws SQLException {
      return active_statement.executeUpdate(s, strings);
    }

    @Override
    public boolean execute(String s, int i) throws SQLException {
      return active_statement.execute(s, i);
    }

    @Override
    public boolean execute(String s, int[] ints) throws SQLException {
      return active_statement.execute(s, ints);
    }

    @Override
    public boolean execute(String s, String[] strings) throws SQLException {
      return active_statement.execute(s, strings);
    }

    @Override
    public int getResultSetHoldability() throws SQLException {
      return active_statement.getResultSetHoldability();
    }

    @Override
    public boolean isClosed() throws SQLException {
      return active_statement.isClosed();
    }

    @Override
    public void setPoolable(boolean b) throws SQLException {
      active_statement.setPoolable(b);
    }

    @Override
    public boolean isPoolable() throws SQLException {
      return active_statement.isPoolable();
    }

    @Override
    public void closeOnCompletion() throws SQLException {
      active_statement.closeOnCompletion();
    }

    @Override
    public boolean isCloseOnCompletion() throws SQLException {
      return active_statement.isCloseOnCompletion();
    }

    @Override
    public long getLargeUpdateCount() throws SQLException {
      return active_statement.getLargeUpdateCount();
    }

    @Override
    public void setLargeMaxRows(long l) throws SQLException {
      active_statement.setLargeMaxRows(l);
    }

    @Override
    public long getLargeMaxRows() throws SQLException {
      return active_statement.getLargeMaxRows();
    }

    @Override
    public long[] executeLargeBatch() throws SQLException {
      return active_statement.executeLargeBatch();
    }

    @Override
    public long executeLargeUpdate(String s) throws SQLException {
      return active_statement.executeLargeUpdate(s);
    }

    @Override
    public long executeLargeUpdate(String s, int i) throws SQLException {
      return active_statement.executeLargeUpdate(s, i);
    }

    @Override
    public long executeLargeUpdate(String s, int[] ints) throws SQLException {
      return active_statement.executeLargeUpdate(s, ints);
    }

    @Override
    public long executeLargeUpdate(String s, String[] strings) throws SQLException {
      return active_statement.executeLargeUpdate(s, strings);
    }

    @Override
    public <T> T unwrap(Class<T> aClass) throws SQLException {
      return active_statement.unwrap(aClass);
    }

    @Override
    public boolean isWrapperFor(Class<?> aClass) throws SQLException {
      return active_statement.isWrapperFor(aClass);
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
