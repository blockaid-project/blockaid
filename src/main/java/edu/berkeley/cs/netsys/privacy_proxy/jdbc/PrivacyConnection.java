package edu.berkeley.cs.netsys.privacy_proxy.jdbc;

import com.google.common.collect.ImmutableList;
import cache.QueryTrace;
import cache.QueryTraceEntry;
import org.apache.calcite.schema.SchemaPlus;
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class PrivacyConnection implements Connection {
  private Connection direct_connection;
  private PrivacyParser parser;
  private final QueryChecker query_checker;
  private ArrayList<Policy> policy_list;
  public QueryTrace current_trace;
  private SchemaPlusWithKey schema;

  PrivacyConnection(Connection direct_connection, Properties direct_info) throws SQLException {
    this.direct_connection = direct_connection;
    Properties info = direct_info;
    info.setProperty("schemaFactory", "catalog.db.SchemaFactory");
    QueryContext ctx;
    try {
      ctx = new QueryContext(info);
    } catch (PrivacyException e){
      throw new SQLException(e.getMessage(), e);
    }
    this.parser = new ParserFactory(ctx).getParser();

    String database_name = info.getProperty("database_name", "PUBLIC");
    SchemaPlus schemaPlus = this.parser.getRootSchma().getSubSchema("CANONICAL").getSubSchema(database_name);

    String deps = info.getProperty("deps");
    String pks = info.getProperty("pk");
    String fks = info.getProperty("fk");

    Map<String, List<String>> primaryKeys = new HashMap<>();
    if (!pks.isEmpty()) {
      for (String pk : pks.split("\n")) {
        pk = pk.toUpperCase();
        String[] parts = pk.split(":", 2);
        String[] columns = parts[1].split(",");
        if (!primaryKeys.containsKey(parts[0])) {
          primaryKeys.put(parts[0], Arrays.asList(columns));
        }
      }
    }

    // TODO(zhangwen): ideally want a tuple of four elements...
    Set<List<String>> foreignKeys = new HashSet<>();
    for (String fk : fks.split("\n")) {
      fk = fk.toUpperCase();
      String[] parts = fk.split(":", 2);
      String[] from = parts[0].split("\\.", 2);
      String[] to = parts[1].split("\\.", 2);
      foreignKeys.add(ImmutableList.of(from[0], from[1], to[0], to[1]));
    }

    schema = new SchemaPlusWithKey(schemaPlus, primaryKeys, foreignKeys);

    this.policy_list = new ArrayList<>();
    set_policy(info, ctx);

    this.query_checker = QueryChecker.getInstance(
            this.policy_list,
            this.schema,
            deps.isEmpty() ? new String[0] : deps.split("\n"),
            pks.isEmpty() ? new String[0] : pks.split("\n"),
            fks.isEmpty() ? new String[0] : fks.split("\n")
    );
    current_trace = new QueryTrace();
  }

  private void set_policy(Properties info, QueryContext ctx) {
    for (String sql : info.getProperty("policy").split("\n")) {
      this.policy_list.add(new Policy(ctx, this.schema, sql));
    }
  }

  /**
   * Parses SQL query and determines whether to apply policies to it.
   * @param query the query to parse.
   * @return parsed query if policies are applicable, empty otherwise.
   * @throws SQLException if parsing fails.
   */
  private Optional<ParserResult> shouldApplyPolicy(String query) throws SQLException {
    if (query.toUpperCase().startsWith("UPDATE")) {
      // The Calcite parser doesn't like our updates--
      // org.apache.calcite.sql.parser.impl.ParseException: Encountered "." at line 1, column 43.
      // Was expecting: "=" ... : UPDATE `notifications` SET `notifications`.`unread` = 0 WHERE
      // `notifications`.`recipient_id` = ? AND `notifications`.`target_type` = ?
      // AND `notifications`.`target_id` = ? AND `notifications`.`unread` = ?
      return Optional.empty();
    }

    // FIXME(zhangwen): HACK-- As Eric reported, Calcite doesn't like "one", and so we append an underscore to it.
    query = query.replace("1 AS one", "1 AS one_");
    ParserResult parser_result = parser.parse(query);

    SqlKind kind = parser_result.getSqlNode().getKind();
    if (kind.equals(SqlKind.SELECT) || kind.equals(SqlKind.ORDER_BY) || kind.equals(SqlKind.UNION)) {
      // These are the types of queries we do handle.
      return Optional.of(parser_result);
    }

    return Optional.empty();
  }

  public void resetSequence() {
    current_trace = new QueryTrace();
  }

  @Override
  public Statement createStatement() throws SQLException {
//    System.out.println("=== createStatement ===");
    return new PrivacyStatement();
  }

  @Override
  public PreparedStatement prepareStatement(String s) throws SQLException {
    Pattern pattern = Pattern.compile("\\?([A-Za-z0-9_]*)");
    Matcher matcher = pattern.matcher(s);
    List<String> paramNames = new ArrayList<>();
    while (matcher.find()) {
      String name = matcher.group(1);
      if (name.isEmpty()) {
        name = "?";
      }
      paramNames.add(name);
    }
    s = matcher.replaceAll("?");
    // FIXME(zhangwen): We'll get rid of any LIMIT clause, but we keep any parameters used by the LIMIT clause.  Bad?

    Optional<ParserResult> parser_result = shouldApplyPolicy(s);
    if (!parser_result.isPresent()) {  // We let this query go through directly.
      return direct_connection.prepareStatement(s);
    }

    return new PrivacyPreparedStatement(s, parser_result.get(), paramNames);
  }

  @Override
  public CallableStatement prepareCall(String s) throws SQLException {
//      System.out.println("=== prepareCall ===");
    return direct_connection.prepareCall(s);
  }

  @Override
  public String nativeSQL(String s) throws SQLException {
//    System.out.println("=== nativeSQL ===");
    return direct_connection.nativeSQL(s);
  }

  @Override
  public void setAutoCommit(boolean b) throws SQLException {
//    System.out.println("=== setAutoCommit ===");
    direct_connection.setAutoCommit(b);
  }

  @Override
  public boolean getAutoCommit() throws SQLException {
//    System.out.println("=== getAutoCommit ===");
    return direct_connection.getAutoCommit();
  }

  @Override
  public void commit() throws SQLException {
//    System.out.println("=== commit ===");
    direct_connection.commit();
  }

  @Override
  public void rollback() throws SQLException {
//    System.out.println("=== rollback ===");
    direct_connection.rollback();
  }

  @Override
  public void close() throws SQLException {
//    System.out.println("=== close ===");
    direct_connection.close();
  }

  @Override
  public boolean isClosed() throws SQLException {
//    System.out.println("=== isClosed ===");
    return direct_connection.isClosed();
  }

  @Override
  public DatabaseMetaData getMetaData() throws SQLException {
//    System.out.println("=== getMetaData ===");
    return direct_connection.getMetaData();
  }

  @Override
  public void setReadOnly(boolean b) throws SQLException {
//    System.out.println("=== setReadOnly ===");
    direct_connection.setReadOnly(b);
  }

  @Override
  public boolean isReadOnly() throws SQLException {
//    System.out.println("=== isReadOnly ===");
    return direct_connection.isReadOnly();
  }

  @Override
  public void setCatalog(String s) throws SQLException {
//    System.out.println("=== setCatalog ===");
    direct_connection.setCatalog(s);
  }

  @Override
  public String getCatalog() throws SQLException {
//    System.out.println("=== getCatalog ===");
    return direct_connection.getCatalog();
  }

  @Override
  public void setTransactionIsolation(int i) throws SQLException {
//    System.out.println("=== setTransactionIsolation ===");
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
//    System.out.println("=== prepareStatement ===");
    return direct_connection.prepareStatement(s, i, i1);
  }

  @Override
  public CallableStatement prepareCall(String s, int i, int i1) throws SQLException {
//    System.out.println("=== prepareCall ===");
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
//    System.out.println("=== rollback ===");
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
//    System.out.println("=== prepareStatement ===");
    return direct_connection.prepareStatement(s, i, i1, i2);
  }

  @Override
  public CallableStatement prepareCall(String s, int i, int i1, int i2) throws SQLException {
//    System.out.println("=== prepareCall ===");
    return direct_connection.prepareCall(s, i, i1, i2);
  }

  @Override
  public PreparedStatement prepareStatement(String s, int i) throws SQLException {
//    System.out.println("=== prepareStatement ===");
    return direct_connection.prepareStatement(s, i);
  }

  @Override
  public PreparedStatement prepareStatement(String s, int[] ints) throws SQLException {
//    System.out.println("=== prepareStatement ===");
    return direct_connection.prepareStatement(s, ints);
  }

  @Override
  public PreparedStatement prepareStatement(String s, String[] strings) throws SQLException {
//    System.out.println("=== prepareStatement ===");
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
//    System.out.println("=== setSchema ===");
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

  public class PrivacyPreparedStatement implements PreparedStatement {
    private PreparedStatement direct_statement;
    private ParserResult parser_result;
    private List<String> param_names;
    private Object[] values;
    private PrivacyQuery privacy_query = null;

    PrivacyPreparedStatement(String sql, ParserResult pr, List<String> param_names) throws SQLException {
      values = new Object[(sql + " ").split("\\?").length - 1];
      this.parser_result = pr;
      direct_statement = direct_connection.prepareStatement(sql, ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
      this.param_names = param_names;
    }

    @Override
    public ResultSet executeQuery() throws SQLException {
      if (!checkPolicy()) {
        throw new SQLException("Privacy compliance was not met");
      }
      return new ResultSetWrapper(direct_statement.executeQuery());
    }

    public boolean checkPolicy() {
      System.out.println("checkPolicy: " + parser_result.getParsedSql() + "\t" + Arrays.toString(values));
      privacy_query = PrivacyQueryFactory.createPrivacyQuery(parser_result, schema, values, param_names);

      current_trace.startQuery(privacy_query, Arrays.asList(values));
      final long startTime = System.currentTimeMillis();
      try {
        return query_checker.checkPolicy(current_trace);
      } catch (Exception e) {
        System.out.println("\t| EXCEPTION:\t" + e);
        throw e;
      } finally {
        final long endTime = System.currentTimeMillis();
        System.out.println("\t+ Policy checking:\t" + (endTime - startTime));
      }
    }

    private void addRow(List<List<Object>> rows, List<Object> row) {
      QueryTraceEntry current = current_trace.getCurrentQuery();
      List<Boolean> resultBitmap = current.getQuery().getResultBitmap();
      for (int i = row.size(); i-- > 0; ) {
        if (i >= resultBitmap.size() || !resultBitmap.get(i)) {
          row.remove(i);
        }
      }
      rows.add(row);
    }

    private class ResultSetWrapper implements ResultSet {
      ResultSet resultSet;
      List<Integer> columnTypes;

      private ResultSetWrapper(ResultSet resultSet) throws SQLException {
        this.resultSet = resultSet;

        ResultSetMetaData metaData = resultSet.getMetaData();
        int columnCount = metaData.getColumnCount();
        columnTypes = new ArrayList<>();
        for (int i = 1; i <= columnCount; ++i) {
          columnTypes.add(metaData.getColumnType(i));
        }

        List<List<Object>> rows = new ArrayList<>();
        while (resultSet.next()) {
          List<Object> row = new ArrayList<>();
          for (int i = 1; i <= columnTypes.size(); ++i) {
            // TODO(zhangwen): NULLs fetched from the DB are currently represented by the default value for the underlying
            //  type (e.g., 0 for int).  We can probably get away with this?
            switch (columnTypes.get(i - 1)) {
              case Types.INTEGER:
              case Types.BIGINT:
              case Types.TINYINT:
              case Types.BIT: // TODO(zhangwen): turn into a Boolean?
                row.add(resultSet.getInt(i));
                break;
              case Types.VARCHAR:
              case Types.LONGVARCHAR:
              case Types.CLOB:
                row.add(resultSet.getString(i));
                break;
              case Types.DECIMAL:
              case Types.DOUBLE:
                row.add(resultSet.getDouble(i));
                break;
              case Types.BOOLEAN:
                row.add(resultSet.getBoolean(i));
                break;
              case Types.DATE:
                Date d = resultSet.getDate(i);
                if (d == null) {
                  row.add(null);
                } else {
                  row.add(d.getTime());
                }
                break;
              case Types.TIMESTAMP:
                Timestamp ts = resultSet.getTimestamp(i);
                if (ts == null) {
                  row.add(null);
                } else {
                  row.add(ts.getTime());
                }
                break;
              default:
                throw new UnsupportedOperationException("unsupported type: " + columnTypes.get(i - 1));
            }
          }
          addRow(rows, row);
        }
        current_trace.endQuery(rows);

        resultSet.beforeFirst();
      }

      @Override
      public boolean next() throws SQLException {
        return resultSet.next();
      }

      @Override
      public void close() throws SQLException {
        resultSet.close();
      }

      @Override
      public boolean wasNull() throws SQLException {
        return resultSet.wasNull();
      }

      @Override
      public String getString(int i) throws SQLException {
        return resultSet.getString(i);
      }

      @Override
      public boolean getBoolean(int i) throws SQLException {
        return resultSet.getBoolean(i);
      }

      @Override
      public byte getByte(int i) throws SQLException {
        return resultSet.getByte(i);
      }

      @Override
      public short getShort(int i) throws SQLException {
        return resultSet.getShort(i);
      }

      @Override
      public int getInt(int i) throws SQLException {
        return resultSet.getInt(i);
      }

      @Override
      public long getLong(int i) throws SQLException {
        return resultSet.getLong(i);
      }

      @Override
      public float getFloat(int i) throws SQLException {
        return resultSet.getFloat(i);
      }

      @Override
      public double getDouble(int i) throws SQLException {
        return resultSet.getDouble(i);
      }

      @Override
      @Deprecated
      public BigDecimal getBigDecimal(int i, int i1) throws SQLException {
        return resultSet.getBigDecimal(i, i1);
      }

      @Override
      public byte[] getBytes(int i) throws SQLException {
        return resultSet.getBytes(i);
      }

      @Override
      public Date getDate(int i) throws SQLException {
        return resultSet.getDate(i);
      }

      @Override
      public Time getTime(int i) throws SQLException {
        return resultSet.getTime(i);
      }

      @Override
      public Timestamp getTimestamp(int i) throws SQLException {
        return resultSet.getTimestamp(i);
      }

      @Override
      public InputStream getAsciiStream(int i) throws SQLException {
        return resultSet.getAsciiStream(i);
      }

      @Override
      @Deprecated
      public InputStream getUnicodeStream(int i) throws SQLException {
        return resultSet.getUnicodeStream(i);
      }

      @Override
      public InputStream getBinaryStream(int i) throws SQLException {
        return resultSet.getBinaryStream(i);
      }

      @Override
      public String getString(String s) throws SQLException {
        return resultSet.getString(s);
      }

      @Override
      public boolean getBoolean(String s) throws SQLException {
        return resultSet.getBoolean(s);
      }

      @Override
      public byte getByte(String s) throws SQLException {
        return resultSet.getByte(s);
      }

      @Override
      public short getShort(String s) throws SQLException {
        return resultSet.getShort(s);
      }

      @Override
      public int getInt(String s) throws SQLException {
        return resultSet.getInt(s);
      }

      @Override
      public long getLong(String s) throws SQLException {
        return resultSet.getLong(s);
      }

      @Override
      public float getFloat(String s) throws SQLException {
        return resultSet.getFloat(s);
      }

      @Override
      public double getDouble(String s) throws SQLException {
        return resultSet.getDouble(s);
      }

      @Override
      @Deprecated
      public BigDecimal getBigDecimal(String s, int i) throws SQLException {
        return resultSet.getBigDecimal(s, i);
      }

      @Override
      public byte[] getBytes(String s) throws SQLException {
        return resultSet.getBytes(s);
      }

      @Override
      public Date getDate(String s) throws SQLException {
        return resultSet.getDate(s);
      }

      @Override
      public Time getTime(String s) throws SQLException {
        return resultSet.getTime(s);
      }

      @Override
      public Timestamp getTimestamp(String s) throws SQLException {
        return resultSet.getTimestamp(s);
      }

      @Override
      public InputStream getAsciiStream(String s) throws SQLException {
        return resultSet.getAsciiStream(s);
      }

      @Override
      @Deprecated
      public InputStream getUnicodeStream(String s) throws SQLException {
        return resultSet.getUnicodeStream(s);
      }

      @Override
      public InputStream getBinaryStream(String s) throws SQLException {
        return resultSet.getBinaryStream(s);
      }

      @Override
      public SQLWarning getWarnings() throws SQLException {
        return resultSet.getWarnings();
      }

      @Override
      public void clearWarnings() throws SQLException {
        resultSet.clearWarnings();
      }

      @Override
      public String getCursorName() throws SQLException {
        return resultSet.getCursorName();
      }

      @Override
      public ResultSetMetaData getMetaData() throws SQLException {
        return resultSet.getMetaData();
      }

      @Override
      public Object getObject(int i) throws SQLException {
        return resultSet.getObject(i);
      }

      @Override
      public Object getObject(String s) throws SQLException {
        return resultSet.getObject(s);
      }

      @Override
      public int findColumn(String s) throws SQLException {
        return resultSet.findColumn(s);
      }

      @Override
      public Reader getCharacterStream(int i) throws SQLException {
        return resultSet.getCharacterStream(i);
      }

      @Override
      public Reader getCharacterStream(String s) throws SQLException {
        return resultSet.getCharacterStream(s);
      }

      @Override
      public BigDecimal getBigDecimal(int i) throws SQLException {
        return resultSet.getBigDecimal(i);
      }

      @Override
      public BigDecimal getBigDecimal(String s) throws SQLException {
        return resultSet.getBigDecimal(s);
      }

      @Override
      public boolean isBeforeFirst() throws SQLException {
        return resultSet.isBeforeFirst();
      }

      @Override
      public boolean isAfterLast() throws SQLException {
        return resultSet.isAfterLast();
      }

      @Override
      public boolean isFirst() throws SQLException {
        return resultSet.isFirst();
      }

      @Override
      public boolean isLast() throws SQLException {
        return resultSet.isLast();
      }

      @Override
      public void beforeFirst() throws SQLException {
        resultSet.beforeFirst();
      }

      @Override
      public void afterLast() throws SQLException {
        resultSet.afterLast();
      }

      @Override
      public boolean first() throws SQLException {
        return resultSet.first();
      }

      @Override
      public boolean last() throws SQLException {
        return resultSet.last();
      }

      @Override
      public int getRow() throws SQLException {
        return resultSet.getRow();
      }

      @Override
      public boolean absolute(int i) throws SQLException {
        return resultSet.absolute(i);
      }

      @Override
      public boolean relative(int i) throws SQLException {
        return resultSet.relative(i);
      }

      @Override
      public boolean previous() throws SQLException {
        return resultSet.previous();
      }

      @Override
      public void setFetchDirection(int i) throws SQLException {
        resultSet.setFetchDirection(i);
      }

      @Override
      public int getFetchDirection() throws SQLException {
        return resultSet.getFetchDirection();
      }

      @Override
      public void setFetchSize(int i) throws SQLException {
        resultSet.setFetchSize(i);
      }

      @Override
      public int getFetchSize() throws SQLException {
        return resultSet.getFetchSize();
      }

      @Override
      public int getType() throws SQLException {
        return resultSet.getType();
      }

      @Override
      public int getConcurrency() throws SQLException {
        return resultSet.getConcurrency();
      }

      @Override
      public boolean rowUpdated() throws SQLException {
        return resultSet.rowUpdated();
      }

      @Override
      public boolean rowInserted() throws SQLException {
        return resultSet.rowInserted();
      }

      @Override
      public boolean rowDeleted() throws SQLException {
        return resultSet.rowDeleted();
      }

      @Override
      public void updateNull(int i) throws SQLException {
        resultSet.updateNull(i);
      }

      @Override
      public void updateBoolean(int i, boolean b) throws SQLException {
        resultSet.updateBoolean(i, b);
      }

      @Override
      public void updateByte(int i, byte b) throws SQLException {
        resultSet.updateByte(i, b);
      }

      @Override
      public void updateShort(int i, short i1) throws SQLException {
        resultSet.updateShort(i, i1);
      }

      @Override
      public void updateInt(int i, int i1) throws SQLException {
        resultSet.updateInt(i, i1);
      }

      @Override
      public void updateLong(int i, long l) throws SQLException {
        resultSet.updateLong(i, l);
      }

      @Override
      public void updateFloat(int i, float v) throws SQLException {
        resultSet.updateFloat(i, v);
      }

      @Override
      public void updateDouble(int i, double v) throws SQLException {
        resultSet.updateDouble(i, v);
      }

      @Override
      public void updateBigDecimal(int i, BigDecimal bigDecimal) throws SQLException {
        resultSet.updateBigDecimal(i, bigDecimal);
      }

      @Override
      public void updateString(int i, String s) throws SQLException {
        resultSet.updateString(i, s);
      }

      @Override
      public void updateBytes(int i, byte[] bytes) throws SQLException {
        resultSet.updateBytes(i, bytes);
      }

      @Override
      public void updateDate(int i, Date date) throws SQLException {
        resultSet.updateDate(i, date);
      }

      @Override
      public void updateTime(int i, Time time) throws SQLException {
        resultSet.updateTime(i, time);
      }

      @Override
      public void updateTimestamp(int i, Timestamp timestamp) throws SQLException {
        resultSet.updateTimestamp(i, timestamp);
      }

      @Override
      public void updateAsciiStream(int i, InputStream inputStream, int i1) throws SQLException {
        resultSet.updateAsciiStream(i, inputStream, i1);
      }

      @Override
      public void updateBinaryStream(int i, InputStream inputStream, int i1) throws SQLException {
        resultSet.updateBinaryStream(i, inputStream, i1);
      }

      @Override
      public void updateCharacterStream(int i, Reader reader, int i1) throws SQLException {
        resultSet.updateCharacterStream(i, reader, i1);
      }

      @Override
      public void updateObject(int i, Object o, int i1) throws SQLException {
        resultSet.updateObject(i, o, i1);
      }

      @Override
      public void updateObject(int i, Object o) throws SQLException {
        resultSet.updateObject(i, o);
      }

      @Override
      public void updateNull(String s) throws SQLException {
        resultSet.updateNull(s);
      }

      @Override
      public void updateBoolean(String s, boolean b) throws SQLException {
        resultSet.updateBoolean(s, b);
      }

      @Override
      public void updateByte(String s, byte b) throws SQLException {
        resultSet.updateByte(s, b);
      }

      @Override
      public void updateShort(String s, short i) throws SQLException {
        resultSet.updateShort(s, i);
      }

      @Override
      public void updateInt(String s, int i) throws SQLException {
        resultSet.updateInt(s, i);
      }

      @Override
      public void updateLong(String s, long l) throws SQLException {
        resultSet.updateLong(s, l);
      }

      @Override
      public void updateFloat(String s, float v) throws SQLException {
        resultSet.updateFloat(s, v);
      }

      @Override
      public void updateDouble(String s, double v) throws SQLException {
        resultSet.updateDouble(s, v);
      }

      @Override
      public void updateBigDecimal(String s, BigDecimal bigDecimal) throws SQLException {
        resultSet.updateBigDecimal(s, bigDecimal);
      }

      @Override
      public void updateString(String s, String s1) throws SQLException {
        resultSet.updateString(s, s1);
      }

      @Override
      public void updateBytes(String s, byte[] bytes) throws SQLException {
        resultSet.updateBytes(s, bytes);
      }

      @Override
      public void updateDate(String s, Date date) throws SQLException {
        resultSet.updateDate(s, date);
      }

      @Override
      public void updateTime(String s, Time time) throws SQLException {
        resultSet.updateTime(s, time);
      }

      @Override
      public void updateTimestamp(String s, Timestamp timestamp) throws SQLException {
        resultSet.updateTimestamp(s, timestamp);
      }

      @Override
      public void updateAsciiStream(String s, InputStream inputStream, int i) throws SQLException {
        resultSet.updateAsciiStream(s, inputStream, i);
      }

      @Override
      public void updateBinaryStream(String s, InputStream inputStream, int i) throws SQLException {
        resultSet.updateBinaryStream(s, inputStream, i);
      }

      @Override
      public void updateCharacterStream(String s, Reader reader, int i) throws SQLException {
        resultSet.updateCharacterStream(s, reader, i);
      }

      @Override
      public void updateObject(String s, Object o, int i) throws SQLException {
        resultSet.updateObject(s, o, i);
      }

      @Override
      public void updateObject(String s, Object o) throws SQLException {
        resultSet.updateObject(s, o);
      }

      @Override
      public void insertRow() throws SQLException {
        resultSet.insertRow();
      }

      @Override
      public void updateRow() throws SQLException {
        resultSet.updateRow();
      }

      @Override
      public void deleteRow() throws SQLException {
        resultSet.deleteRow();
      }

      @Override
      public void refreshRow() throws SQLException {
        resultSet.refreshRow();
      }

      @Override
      public void cancelRowUpdates() throws SQLException {
        resultSet.cancelRowUpdates();
      }

      @Override
      public void moveToInsertRow() throws SQLException {
        resultSet.moveToInsertRow();
      }

      @Override
      public void moveToCurrentRow() throws SQLException {
        resultSet.moveToCurrentRow();
      }

      @Override
      public Statement getStatement() throws SQLException {
        return resultSet.getStatement();
      }

      @Override
      public Object getObject(int i, Map<String, Class<?>> map) throws SQLException {
        return resultSet.getObject(i, map);
      }

      @Override
      public Ref getRef(int i) throws SQLException {
        return resultSet.getRef(i);
      }

      @Override
      public Blob getBlob(int i) throws SQLException {
        return resultSet.getBlob(i);
      }

      @Override
      public Clob getClob(int i) throws SQLException {
        return resultSet.getClob(i);
      }

      @Override
      public Array getArray(int i) throws SQLException {
        return resultSet.getArray(i);
      }

      @Override
      public Object getObject(String s, Map<String, Class<?>> map) throws SQLException {
        return resultSet.getObject(s, map);
      }

      @Override
      public Ref getRef(String s) throws SQLException {
        return resultSet.getRef(s);
      }

      @Override
      public Blob getBlob(String s) throws SQLException {
        return resultSet.getBlob(s);
      }

      @Override
      public Clob getClob(String s) throws SQLException {
        return resultSet.getClob(s);
      }

      @Override
      public Array getArray(String s) throws SQLException {
        return resultSet.getArray(s);
      }

      @Override
      public Date getDate(int i, Calendar calendar) throws SQLException {
        return resultSet.getDate(i, calendar);
      }

      @Override
      public Date getDate(String s, Calendar calendar) throws SQLException {
        return resultSet.getDate(s, calendar);
      }

      @Override
      public Time getTime(int i, Calendar calendar) throws SQLException {
        return resultSet.getTime(i, calendar);
      }

      @Override
      public Time getTime(String s, Calendar calendar) throws SQLException {
        return resultSet.getTime(s, calendar);
      }

      @Override
      public Timestamp getTimestamp(int i, Calendar calendar) throws SQLException {
        return resultSet.getTimestamp(i, calendar);
      }

      @Override
      public Timestamp getTimestamp(String s, Calendar calendar) throws SQLException {
        return resultSet.getTimestamp(s, calendar);
      }

      @Override
      public URL getURL(int i) throws SQLException {
        return resultSet.getURL(i);
      }

      @Override
      public URL getURL(String s) throws SQLException {
        return resultSet.getURL(s);
      }

      @Override
      public void updateRef(int i, Ref ref) throws SQLException {
        resultSet.updateRef(i, ref);
      }

      @Override
      public void updateRef(String s, Ref ref) throws SQLException {
        resultSet.updateRef(s, ref);
      }

      @Override
      public void updateBlob(int i, Blob blob) throws SQLException {
        resultSet.updateBlob(i, blob);
      }

      @Override
      public void updateBlob(String s, Blob blob) throws SQLException {
        resultSet.updateBlob(s, blob);
      }

      @Override
      public void updateClob(int i, Clob clob) throws SQLException {
        resultSet.updateClob(i, clob);
      }

      @Override
      public void updateClob(String s, Clob clob) throws SQLException {
        resultSet.updateClob(s, clob);
      }

      @Override
      public void updateArray(int i, Array array) throws SQLException {
        resultSet.updateArray(i, array);
      }

      @Override
      public void updateArray(String s, Array array) throws SQLException {
        resultSet.updateArray(s, array);
      }

      @Override
      public RowId getRowId(int i) throws SQLException {
        return resultSet.getRowId(i);
      }

      @Override
      public RowId getRowId(String s) throws SQLException {
        return resultSet.getRowId(s);
      }

      @Override
      public void updateRowId(int i, RowId rowId) throws SQLException {
        resultSet.updateRowId(i, rowId);
      }

      @Override
      public void updateRowId(String s, RowId rowId) throws SQLException {
        resultSet.updateRowId(s, rowId);
      }

      @Override
      public int getHoldability() throws SQLException {
        return resultSet.getHoldability();
      }

      @Override
      public boolean isClosed() throws SQLException {
        return resultSet.isClosed();
      }

      @Override
      public void updateNString(int i, String s) throws SQLException {
        resultSet.updateNString(i, s);
      }

      @Override
      public void updateNString(String s, String s1) throws SQLException {
        resultSet.updateNString(s, s1);
      }

      @Override
      public void updateNClob(int i, NClob nClob) throws SQLException {
        resultSet.updateNClob(i, nClob);
      }

      @Override
      public void updateNClob(String s, NClob nClob) throws SQLException {
        resultSet.updateNClob(s, nClob);
      }

      @Override
      public NClob getNClob(int i) throws SQLException {
        return resultSet.getNClob(i);
      }

      @Override
      public NClob getNClob(String s) throws SQLException {
        return resultSet.getNClob(s);
      }

      @Override
      public SQLXML getSQLXML(int i) throws SQLException {
        return resultSet.getSQLXML(i);
      }

      @Override
      public SQLXML getSQLXML(String s) throws SQLException {
        return resultSet.getSQLXML(s);
      }

      @Override
      public void updateSQLXML(int i, SQLXML sqlxml) throws SQLException {
        resultSet.updateSQLXML(i, sqlxml);
      }

      @Override
      public void updateSQLXML(String s, SQLXML sqlxml) throws SQLException {
        resultSet.updateSQLXML(s, sqlxml);
      }

      @Override
      public String getNString(int i) throws SQLException {
        return resultSet.getNString(i);
      }

      @Override
      public String getNString(String s) throws SQLException {
        return resultSet.getNString(s);
      }

      @Override
      public Reader getNCharacterStream(int i) throws SQLException {
        return resultSet.getNCharacterStream(i);
      }

      @Override
      public Reader getNCharacterStream(String s) throws SQLException {
        return resultSet.getNCharacterStream(s);
      }

      @Override
      public void updateNCharacterStream(int i, Reader reader, long l) throws SQLException {
        resultSet.updateNCharacterStream(i, reader, l);
      }

      @Override
      public void updateNCharacterStream(String s, Reader reader, long l) throws SQLException {
        resultSet.updateNCharacterStream(s, reader, l);
      }

      @Override
      public void updateAsciiStream(int i, InputStream inputStream, long l) throws SQLException {
        resultSet.updateAsciiStream(i, inputStream, l);
      }

      @Override
      public void updateBinaryStream(int i, InputStream inputStream, long l) throws SQLException {
        resultSet.updateBinaryStream(i, inputStream, l);
      }

      @Override
      public void updateCharacterStream(int i, Reader reader, long l) throws SQLException {
        resultSet.updateCharacterStream(i, reader, l);
      }

      @Override
      public void updateAsciiStream(String s, InputStream inputStream, long l) throws SQLException {
        resultSet.updateAsciiStream(s, inputStream, l);
      }

      @Override
      public void updateBinaryStream(String s, InputStream inputStream, long l) throws SQLException {
        resultSet.updateBinaryStream(s, inputStream, l);
      }

      @Override
      public void updateCharacterStream(String s, Reader reader, long l) throws SQLException {
        resultSet.updateCharacterStream(s, reader, l);
      }

      @Override
      public void updateBlob(int i, InputStream inputStream, long l) throws SQLException {
        resultSet.updateBlob(i, inputStream, l);
      }

      @Override
      public void updateBlob(String s, InputStream inputStream, long l) throws SQLException {
        resultSet.updateBlob(s, inputStream, l);
      }

      @Override
      public void updateClob(int i, Reader reader, long l) throws SQLException {
        resultSet.updateClob(i, reader, l);
      }

      @Override
      public void updateClob(String s, Reader reader, long l) throws SQLException {
        resultSet.updateClob(s, reader, l);
      }

      @Override
      public void updateNClob(int i, Reader reader, long l) throws SQLException {
        resultSet.updateNClob(i, reader, l);
      }

      @Override
      public void updateNClob(String s, Reader reader, long l) throws SQLException {
        resultSet.updateNClob(s, reader, l);
      }

      @Override
      public void updateNCharacterStream(int i, Reader reader) throws SQLException {
        resultSet.updateNCharacterStream(i, reader);
      }

      @Override
      public void updateNCharacterStream(String s, Reader reader) throws SQLException {
        resultSet.updateNCharacterStream(s, reader);
      }

      @Override
      public void updateAsciiStream(int i, InputStream inputStream) throws SQLException {
        resultSet.updateAsciiStream(i, inputStream);
      }

      @Override
      public void updateBinaryStream(int i, InputStream inputStream) throws SQLException {
        resultSet.updateBinaryStream(i, inputStream);
      }

      @Override
      public void updateCharacterStream(int i, Reader reader) throws SQLException {
        resultSet.updateCharacterStream(i, reader);
      }

      @Override
      public void updateAsciiStream(String s, InputStream inputStream) throws SQLException {
        resultSet.updateAsciiStream(s, inputStream);
      }

      @Override
      public void updateBinaryStream(String s, InputStream inputStream) throws SQLException {
        resultSet.updateBinaryStream(s, inputStream);
      }

      @Override
      public void updateCharacterStream(String s, Reader reader) throws SQLException {
        resultSet.updateCharacterStream(s, reader);
      }

      @Override
      public void updateBlob(int i, InputStream inputStream) throws SQLException {
        resultSet.updateBlob(i, inputStream);
      }

      @Override
      public void updateBlob(String s, InputStream inputStream) throws SQLException {
        resultSet.updateBlob(s, inputStream);
      }

      @Override
      public void updateClob(int i, Reader reader) throws SQLException {
        resultSet.updateClob(i, reader);
      }

      @Override
      public void updateClob(String s, Reader reader) throws SQLException {
        resultSet.updateClob(s, reader);
      }

      @Override
      public void updateNClob(int i, Reader reader) throws SQLException {
        resultSet.updateNClob(i, reader);
      }

      @Override
      public void updateNClob(String s, Reader reader) throws SQLException {
        resultSet.updateNClob(s, reader);
      }

      @Override
      public <T> T getObject(int i, Class<T> aClass) throws SQLException {
        return resultSet.getObject(i, aClass);
      }

      @Override
      public <T> T getObject(String s, Class<T> aClass) throws SQLException {
        return resultSet.getObject(s, aClass);
      }

      @Override
      public void updateObject(int i, Object o, SQLType sqlType, int i1) throws SQLException {
        resultSet.updateObject(i, o, sqlType, i1);
      }

      @Override
      public void updateObject(String s, Object o, SQLType sqlType, int i) throws SQLException {
        resultSet.updateObject(s, o, sqlType, i);
      }

      @Override
      public void updateObject(int i, Object o, SQLType sqlType) throws SQLException {
        resultSet.updateObject(i, o, sqlType);
      }

      @Override
      public void updateObject(String s, Object o, SQLType sqlType) throws SQLException {
        resultSet.updateObject(s, o, sqlType);
      }

      @Override
      public <T> T unwrap(Class<T> aClass) throws SQLException {
        return resultSet.unwrap(aClass);
      }

      @Override
      public boolean isWrapperFor(Class<?> aClass) throws SQLException {
        return resultSet.isWrapperFor(aClass);
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
      Arrays.fill(values, null);
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
//      System.out.println("PrivacyPreparedStatement.execute");
      if (!checkPolicy()) {
        throw new SQLException("Privacy compliance was not met");
      }
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
//      System.out.println("PrivacyPreparedStatement.getResultSet");
      // TODO(zhangwen): Is this right?
      ResultSet rs = direct_statement.getResultSet();
      if (rs == null) {
        return null;
      }
      return new ResultSetWrapper(rs);
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
    private Statement active_statment;

    private PrivacyStatement() throws SQLException {
      this.active_statment = direct_connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_UPDATABLE);
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
      Optional<Boolean> r = processSetConst(s);
      if (r.isPresent()) {
        return r.get();
      }
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

    /**
     * Detects whether the query is a special query that sets the value of a constant, and if so, executes the request
     * by adding the (constant name, value) pair to the current sequence.
     * The syntax for such special queries is like: SET @_MY_UID = 2.
     * Currently only supports integer values.
     * @param query the query to check.
     * @return empty if the query is not a set const query, otherwise, the return value of execute.
     */
    private Optional<Boolean> processSetConst(String query) throws SQLException {
      // I made up this syntax.
      Pattern pattern = Pattern.compile("^SET @(_[A-Za-z0-9_]+) = (\\d+)$");
      Matcher matcher = pattern.matcher(query);
      if (!matcher.find()) {
        return Optional.empty();
      }

      String name = matcher.group(1);
      String value = matcher.group(2);
      System.out.println("=== processSetConst: " + name + " = " + value);
      // FIXME(zhangwen): HACK-- resetting the sequence here; DOESN'T WORK if a connection sets multiple consts.
      resetSequence();
      current_trace.setConstValue(name, Integer.valueOf(value));

      // TODO(zhangwen): Can I get away with not actually executing this command?
      return Optional.of(false);
    }

    @Override
    public boolean execute(String s, int i) throws SQLException {
//      System.out.println("=== PrivacyStatement.execute: " + s);
      Optional<Boolean> r = processSetConst(s);
      if (r.isPresent()) {
        return r.get();
      }
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
