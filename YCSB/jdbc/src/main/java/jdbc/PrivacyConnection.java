package jdbc;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import sql.PrivacyQuery;

import java.sql.*;
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

  PrivacyConnection(Connection proxy_connection, Connection direct_connection) {
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
  }

  private boolean checkQueryCompliance(PrivacyQuery query){
      try{
          return policy_decision_cache.get(query);
      } catch (ExecutionException e){
          throw propagate(e);
      }
  }

  private Connection pickConnection(String query) {
//      if (checkQueryCompliance(query)) {
//      if (Math.random() < 0.8) { // -- doesn't work, prepareStatement only called once/query type
      if (false) {
          return this.direct_connection;
      } else {
          return this.proxy_connection;
      }
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
    return pickConnection(s).prepareStatement(s);
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
