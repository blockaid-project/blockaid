package fatjdbc;

import com.google.common.cache.*;
import org.apache.calcite.DataContext;
import org.apache.calcite.avatica.AvaticaParameter;
import org.apache.calcite.avatica.AvaticaPreparedStatement;
import org.apache.calcite.avatica.AvaticaStatement;
import org.apache.calcite.avatica.AvaticaUtils;
import org.apache.calcite.avatica.ColumnMetaData;
import org.apache.calcite.avatica.Meta;
import org.apache.calcite.avatica.MetaImpl;
import org.apache.calcite.avatica.NoSuchStatementException;
import org.apache.calcite.avatica.QueryState;
import org.apache.calcite.avatica.SqlType;
import org.apache.calcite.avatica.remote.TypedValue;
import org.apache.calcite.jdbc.CalcitePrepare;
import org.apache.calcite.jdbc.CalciteSchema;
import org.apache.calcite.linq4j.Enumerable;
import org.apache.calcite.linq4j.Linq4j;
import org.apache.calcite.linq4j.function.Function1;
import org.apache.calcite.linq4j.function.Functions;
import org.apache.calcite.linq4j.function.Predicate1;
import org.apache.calcite.rel.RelCollation;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeFactoryImpl;
import org.apache.calcite.rel.type.RelDataTypeField;
import org.apache.calcite.rel.type.RelDataTypeSystem;
import org.apache.calcite.runtime.FlatLists;
import org.apache.calcite.schema.Table;
import org.apache.calcite.sql.SqlJdbcFunctionCall;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.util.Util;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;

import policy_checker.Policy;
import sql.ParserResult;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import policy_checker.QueryChecker;

import sql.PrivacyException;
import sql.PrivacyQuery;
import sql.PrivacyQueryFactory;

import java.lang.reflect.Field;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.DriverManager;
import java.sql.ParameterMetaData;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.ResultSetMetaData;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Types;
import java.util.*;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.regex.Pattern;


public class PrivacyMetaImpl extends MetaImpl {
    private static final Logger LOG = LoggerFactory.getLogger(PrivacyMetaImpl.class);

    private static final String CONN_CACHE_KEY_BASE = "quark.connectioncache";

    private static final String STMT_CACHE_KEY_BASE = "quark.statementcache";

    /**
     * Special value for {@link Statement#getMaxRows()} that means fetch
     * an unlimited number of rows in a single batch.
     *
     * Any other negative value will return an unlimited number of rows but
     * will do it in the default batch size, namely 100.
     */
    public static final long UNLIMITED_COUNT = -2L;
    public static final int QUERY_TIMEOUT = 60;

    final Calendar calendar = Calendar.getInstance();

    private final String url;
    private final Properties info;
    private final Cache<String, Connection> connectionCache;
    private final Cache<Integer, StatementInfo> statementCache;
    private final HashMap<Policy, LoadingCache<PrivacyQuery, Boolean>> policyCache;
    private final QueryChecker queryChecker;
    private ArrayList<Policy> policy_list;

    /**
     * Generates ids for statements. The ids are unique across all connections
     * created by this JdbcMeta.
     */
    private final AtomicInteger statementIdGenerator = new AtomicInteger();

    public PrivacyMetaImpl(PrivacyConnectionImpl connection, Properties info) {
        super(connection);
        this.info = info;
        this.url = info.getProperty("url");

        int concurrencyLevel = Integer.parseInt(
                info.getProperty(ConnectionCacheSettings.CONCURRENCY_LEVEL.key,
                        ConnectionCacheSettings.CONCURRENCY_LEVEL.defaultValue));
        int initialCapacity = Integer.parseInt(
                info.getProperty(ConnectionCacheSettings.INITIAL_CAPACITY.key,
                        ConnectionCacheSettings.INITIAL_CAPACITY.defaultValue));
        int maxCapacity = Integer.parseInt(
                info.getProperty(ConnectionCacheSettings.MAX_CAPACITY.key,
                        ConnectionCacheSettings.MAX_CAPACITY.defaultValue));
        long connectionExpiryDuration = Long.parseLong(
                info.getProperty(ConnectionCacheSettings.EXPIRY_DURATION.key,
                        ConnectionCacheSettings.EXPIRY_DURATION.defaultValue));
        TimeUnit connectionExpiryUnit = TimeUnit.valueOf(
                info.getProperty(ConnectionCacheSettings.EXPIRY_UNIT.key,
                        ConnectionCacheSettings.EXPIRY_UNIT.defaultValue));

        this.connectionCache = CacheBuilder.newBuilder()
                .concurrencyLevel(concurrencyLevel)
                .initialCapacity(initialCapacity)
                .maximumSize(maxCapacity)
                .expireAfterAccess(connectionExpiryDuration, connectionExpiryUnit)
                .removalListener(new ConnectionExpiryHandler())
                .build();

        concurrencyLevel = Integer.parseInt(
                info.getProperty(StatementCacheSettings.CONCURRENCY_LEVEL.key(),
                        StatementCacheSettings.CONCURRENCY_LEVEL.defaultValue()));
        initialCapacity = Integer.parseInt(
                info.getProperty(StatementCacheSettings.INITIAL_CAPACITY.key(),
                        StatementCacheSettings.INITIAL_CAPACITY.defaultValue()));
        maxCapacity = Integer.parseInt(
                info.getProperty(StatementCacheSettings.MAX_CAPACITY.key(),
                        StatementCacheSettings.MAX_CAPACITY.defaultValue()));
        connectionExpiryDuration = Long.parseLong(
                info.getProperty(StatementCacheSettings.EXPIRY_DURATION.key(),
                        StatementCacheSettings.EXPIRY_DURATION.defaultValue()));
        connectionExpiryUnit = TimeUnit.valueOf(
                info.getProperty(StatementCacheSettings.EXPIRY_UNIT.key(),
                        StatementCacheSettings.EXPIRY_UNIT.defaultValue()));
        this.statementCache = CacheBuilder.newBuilder()
                .concurrencyLevel(concurrencyLevel)
                .initialCapacity(initialCapacity)
                .maximumSize(maxCapacity)
                .expireAfterAccess(connectionExpiryDuration, connectionExpiryUnit)
                .removalListener(new StatementExpiryHandler())
                .build();

        this.policyCache = new HashMap<>();
        this.policy_list = new ArrayList<>();
        set_policy(info);
        this.queryChecker = new QueryChecker(this.policy_list);
        initializePolicyCache();
        System.out.println("end of constructor in privacy meta impl");
    }

    private void set_policy(Properties info) {
        String token = info.getProperty("userRole");
        String[] sqlpolicy;
        switch(token != null ? token : "no_policy_set"){
            case "controller":
                sqlpolicy = new String[]{"select * from blah", "select a, b from blah"};
                break;
            case "processor":
                sqlpolicy = new String[]{"select * from blah", "select a, b from blah"};
                break;
            default:
                sqlpolicy = new String[]{""};
                System.out.println("No policies set. Invalid user policy");
        }
        Policy p1 = new Policy(info, sqlpolicy);
        if (p1 != null)
            this.policy_list.add(p1);
    }

    // Initialize each policy with it's own cache.
    private void initializePolicyCache() {
        for (Policy p : this.policy_list){
            // Just some random settings
            LoadingCache<PrivacyQuery, Boolean> cache = CacheBuilder.newBuilder()
                    .expireAfterAccess(100000, TimeUnit.SECONDS)
                    .maximumSize(50)
                    .build(new CacheLoader<PrivacyQuery, Boolean>() {
                        @Override
                        public Boolean load(final PrivacyQuery query) throws Exception {
                            System.out.println("Cache miss");
                            return getQueryChecker().check_policy(query, p);
                        }
                    });
            this.policyCache.put(p, cache);
        }
    }

    public QueryChecker getQueryChecker()
    {
        return this.queryChecker;
    }


    static <T extends Named> Predicate1<T> namedMatcher(final Pat pattern) {
        if (pattern.s == null || pattern.s.equals("%")) {
            return Functions.truePredicate1();
        }
        final Pattern regex = likeToRegex(pattern);
        return new Predicate1<T>() {
            public boolean apply(T v1) {
                return regex.matcher(v1.getName()).matches();
            }
        };
    }

    static Predicate1<String> matcher(final Pat pattern) {
        if (pattern.s == null || pattern.s.equals("%")) {
            return Functions.truePredicate1();
        }
        final Pattern regex = likeToRegex(pattern);
        return new Predicate1<String>() {
            public boolean apply(String v1) {
                return regex.matcher(v1).matches();
            }
        };
    }

    /** Converts a LIKE-style pattern (where '%' represents a wild-card, escaped
     * using '\') to a Java regex. */
    public static Pattern likeToRegex(Pat pattern) {
        StringBuilder buf = new StringBuilder("^");
        char[] charArray = pattern.s.toCharArray();
        int slash = -2;
        for (int i = 0; i < charArray.length; i++) {
            char c = charArray[i];
            if (slash == i - 1) {
                buf.append('[').append(c).append(']');
            } else {
                switch (c) {
                    case '\\':
                        slash = i;
                        break;
                    case '%':
                        buf.append(".*");
                        break;
                    case '[':
                        buf.append("\\[");
                        break;
                    case ']':
                        buf.append("\\]");
                        break;
                    default:
                        buf.append('[').append(c).append(']');
                }
            }
        }
        buf.append("$");
        return Pattern.compile(buf.toString());
    }

    @Override
    public StatementHandle createStatement(ConnectionHandle ch) {
        final StatementHandle h = super.createStatement(ch);
        final PrivacyConnectionImpl privacyConnection = getConnection();
        privacyConnection.server.addStatement(privacyConnection, h);
        return h;
    }

    @Override
    public void closeStatement(StatementHandle h) {
        final PrivacyConnectionImpl privacyConnection = getConnection();
        PrivacyJdbcStatement stmt = privacyConnection.server.getStatement(h);
        // stmt.close(); // TODO: implement
        privacyConnection.server.removeStatement(h);
    }

    private <E> MetaResultSet createResultSet(Enumerable<E> enumerable,
                                              Class clazz, String... names) {
        final List<ColumnMetaData> columns = new ArrayList<>();
        final List<Field> fields = new ArrayList<>();
        final List<String> fieldNames = new ArrayList<>();
        for (String name : names) {
            final int index = fields.size();
            final String fieldName = AvaticaUtils.toCamelCase(name);
            final Field field;
            try {
                field = clazz.getField(fieldName);
            } catch (NoSuchFieldException e) {
                throw new RuntimeException(e);
            }
            columns.add(columnMetaData(name, index, field.getType(), false));
            fields.add(field);
            fieldNames.add(fieldName);
        }
        //noinspection unchecked
        final Iterable<Object> iterable = (Iterable<Object>) (Iterable) enumerable;
        return createResultSet(Collections.<String, Object>emptyMap(),
                columns, CursorFactory.record(clazz, fields, fieldNames),
                new Frame(0, true, iterable));
    }

    @Override protected <E> MetaResultSet
    createEmptyResultSet(final Class<E> clazz) {
        final List<ColumnMetaData> columns = fieldMetaData(clazz).columns;
        final CursorFactory cursorFactory = CursorFactory.deduce(columns, clazz);
        return createResultSet(Collections.<String, Object>emptyMap(), columns,
                cursorFactory, Frame.EMPTY);
    }

    protected MetaResultSet createResultSet(
            Map<String, Object> internalParameters, List<ColumnMetaData> columns,
            CursorFactory cursorFactory, final Frame firstFrame) {
        try {
            final PrivacyConnectionImpl connection = getConnection();
            final AvaticaStatement statement = connection.createStatement();
            final CalcitePrepare.CalciteSignature<Object> signature =
                    new CalcitePrepare.CalciteSignature<Object>("",
                            ImmutableList.<AvaticaParameter>of(), internalParameters, null,
                            columns, cursorFactory, null, ImmutableList.<RelCollation>of(), -1,
                            null, Meta.StatementType.SELECT) {
                        @Override public Enumerable<Object> enumerable(
                                DataContext dataContext) {
                            return Linq4j.asEnumerable(firstFrame.rows);
                        }
                    };
            return MetaResultSet.create(connection.id, statement.getId(), true,
                    signature, firstFrame);
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    PrivacyConnectionImpl getConnection() {
        return (PrivacyConnectionImpl) connection;
    }

    @Override public Map<DatabaseProperty, Object> getDatabaseProperties(ConnectionHandle ch) {
        final ImmutableMap.Builder<DatabaseProperty, Object> builder =
                ImmutableMap.builder();
        for (DatabaseProperty p : DatabaseProperty.values()) {
            addProperty(builder, p);
        }
        return builder.build();
    }

    private ImmutableMap.Builder<DatabaseProperty, Object> addProperty(
            ImmutableMap.Builder<DatabaseProperty, Object> builder,
            DatabaseProperty p) {
        switch (p) {
            case GET_S_Q_L_KEYWORDS:
                return builder.put(p,
                        SqlParser.create("").getMetadata().getJdbcKeywords());
            case GET_NUMERIC_FUNCTIONS:
                return builder.put(p, SqlJdbcFunctionCall.getNumericFunctions());
            case GET_STRING_FUNCTIONS:
                return builder.put(p, SqlJdbcFunctionCall.getStringFunctions());
            case GET_SYSTEM_FUNCTIONS:
                return builder.put(p, SqlJdbcFunctionCall.getSystemFunctions());
            case GET_TIME_DATE_FUNCTIONS:
                return builder.put(p, SqlJdbcFunctionCall.getTimeDateFunctions());
            default:
                return builder;
        }
    }

    @Override
    public Meta.StatementHandle prepare(Meta.ConnectionHandle ch, String sql,
                                        long maxRowCount) {
        System.out.println("in prepare in privacymetaimpl");
        final Meta.StatementHandle h = createStatement(ch);
        final PrivacyConnectionImpl privacyConnection = getConnection();

        PrivacyJdbcStatement statement = privacyConnection.server.getStatement(h);
        statement.setSignature(h.signature);
        return h;
    }

    private boolean shouldApplyPolicy(SqlKind kind)
    {
        if (kind.equals(kind.SELECT)){
            return true;
        }
        else
            return false;
    }

    public Meta.ExecuteResult prepareAndExecute(Meta.StatementHandle h,
                                                String sql,
                                                long maxRowCount,
                                                Meta.PrepareCallback callback) {
        System.out.println("in prepareandexecute in privacymetaimpl");

        // Create callback, execute query
        try {
            MetaResultSet metaResultSet = null;
            synchronized (callback.getMonitor()) {
                callback.clear();
                ParserResult result = getConnection().parse(sql);

                if (shouldApplyPolicy(result.getSqlNode().getKind())) {
                    PrivacyQuery query = PrivacyQueryFactory.createPrivacyQuery(result);
                    if (checkQueryCompliance(query) == false) {
                        System.out.println("Query {} does not comply".format(sql));
                        return null;
                    }
                }
                metaResultSet = new PlanExecutor(h, getConnection(),
                        connectionCache, maxRowCount).execute(result);
                callback.assign(metaResultSet.signature, metaResultSet.firstFrame,
                        metaResultSet.updateCount);
            }
            callback.execute();
            return new ExecuteResult(ImmutableList.of(metaResultSet));
        } catch (Exception e) {
            throw propagate(e);
        }

    }

    public boolean checkQueryCompliance(PrivacyQuery query){
        System.out.println("Check query compliance");
        for(Map.Entry<Policy, LoadingCache<PrivacyQuery, Boolean>> policy_cache: policyCache.entrySet()){
            boolean compliance;
            try{
                System.out.println("getting value");
                compliance = policy_cache.getValue().get(query);
                System.out.println("got value");
                if (!compliance) {
                    return Boolean.FALSE;
                }
            } catch (ExecutionException e){
                throw propagate(e);
            }
        }
        System.out.println("finished looking at policies");
        return Boolean.TRUE;
    }

    @Override
    public ExecuteResult prepareAndExecute(StatementHandle statementHandle, String sql,
                                           long maxRowCount,
                                           int maxRowsInFirstFrame,
                                           PrepareCallback prepareCallback)
            throws NoSuchStatementException {
        System.out.println("in prepareAndExecute2 in privacymetaimpl");
        System.out.println("in prepareandexecute2" + sql);
        set_policy(this.info);

        try {
            MetaResultSet metaResultSet;
            synchronized (prepareCallback.getMonitor()) {
                prepareCallback.clear();
                ParserResult result = getConnection().parse(sql);

                // DML commands should bypass policy checking
                System.out.println("The type is wefe " + result.getSqlNode().getKind());
                if (shouldApplyPolicy(result.getKind())) {
                    PrivacyQuery query = PrivacyQueryFactory.createPrivacyQuery(result);
                    if (checkQueryCompliance(query) == false) {
                        System.out.println("Query {} does not comply".format(sql));
                        return null;
                    }
                    else{
                        System.out.println("Query does comply!");
                    }
                }

                metaResultSet = new PlanExecutor(statementHandle, getConnection(),
                        connectionCache, maxRowCount).execute(result);
                prepareCallback.assign(metaResultSet.signature, metaResultSet.firstFrame,
                        metaResultSet.updateCount);
            }
            System.out.println("about to execute callback");
            prepareCallback.execute();
            return new ExecuteResult(ImmutableList.of(metaResultSet));
        } catch (Exception e) {
            throw propagate(e);
        }

    }

    @Override
    public ExecuteBatchResult prepareAndExecuteBatch(StatementHandle statementHandle,
                                                     List<String> list)
            throws NoSuchStatementException {
        return null;
    }

    @Override
    public ExecuteBatchResult executeBatch(StatementHandle statementHandle,
                                           List<List<TypedValue>> list)
            throws NoSuchStatementException {
        return null;
    }

    @Override
    public void openConnection(ConnectionHandle ch, Map<String, String> info) {
        LOG.debug("Open Connection:" + ch.id);
        Properties fullInfo = new Properties();
        fullInfo.putAll(this.info);
        if (info != null) {
            fullInfo.putAll(info);
        }

        synchronized (this) {
            try {
                if (connectionCache.asMap().containsKey(ch.id)) {
                    throw new RuntimeException("Connection already exists: " + ch.id);
                }
                Connection conn = DriverManager.getConnection(url, fullInfo);
                connectionCache.put(ch.id, conn);
            } catch (SQLException e) {
                throw new RuntimeException(e);
            }
        }
    }

    @Override
    public void closeConnection(ConnectionHandle ch) {
        Connection conn = connectionCache.getIfPresent(ch.id);
        if (conn == null) {
            LOG.debug("client requested close unknown connection " + ch);
            return;
        }
        if (LOG.isTraceEnabled()) {
            LOG.trace("closing connection " + ch);
        }
        try {
            conn.close();
        } catch (SQLException e) {
            throw propagate(e);
        } finally {
            connectionCache.invalidate(ch.id);
        }
    }

    public MetaResultSet getTables(ConnectionHandle ch,
                                   String catalog,
                                   final Pat schemaPattern,
                                   final Pat tableNamePattern,
                                   final List<String> typeList) {
        final Predicate1<MetaTable> typeFilter;
        if (typeList == null) {
            typeFilter = Functions.truePredicate1();
        } else {
            typeFilter = new Predicate1<MetaTable>() {
                public boolean apply(MetaTable v1) {
                    return typeList.contains(v1.tableType);
                }
            };
        }
        final Predicate1<MetaSchema> schemaMatcher = namedMatcher(schemaPattern);
        try {
            return createResultSet(schemas(catalog)
                            .where(schemaMatcher)
                            .selectMany(
                                    new Function1<MetaSchema, Enumerable<MetaTable>>() {
                                        public Enumerable<MetaTable> apply(MetaSchema schema) {
                                            return tables(schema, matcher(tableNamePattern));
                                        }
                                    })
                            .where(typeFilter),
                    MetaTable.class,
                    "TABLE_CAT",
                    "TABLE_SCHEM",
                    "TABLE_NAME",
                    "TABLE_TYPE",
                    "REMARKS",
                    "TYPE_CAT",
                    "TYPE_SCHEM",
                    "TYPE_NAME",
                    "SELF_REFERENCING_COL_NAME",
                    "REF_GENERATION");
        } catch (PrivacyException e) {
            e.printStackTrace();
            throw new RuntimeException(
                    "parse failed: " + e.getMessage(), e);
        }
    }

    public MetaResultSet getTypeInfo(ConnectionHandle ch) {
        return createResultSet(allTypeInfo(),
                MetaTypeInfo.class,
                "TYPE_NAME",
                "DATA_TYPE",
                "PRECISION",
                "LITERAL_PREFIX",
                "LITERAL_SUFFIX",
                "CREATE_PARAMS",
                "NULLABLE",
                "CASE_SENSITIVE",
                "SEARCHABLE",
                "UNSIGNED_ATTRIBUTE",
                "FIXED_PREC_SCALE",
                "AUTO_INCREMENT",
                "LOCAL_TYPE_NAME",
                "MINIMUM_SCALE",
                "MAXIMUM_SCALE",
                "SQL_DATA_TYPE",
                "SQL_DATETIME_SUB",
                "NUM_PREC_RADIX");
    }

    public MetaResultSet getColumns(ConnectionHandle ch,
                                    String catalog,
                                    Pat schemaPattern,
                                    Pat tableNamePattern,
                                    Pat columnNamePattern) {
        final Predicate1<String> tableNameMatcher = matcher(tableNamePattern);
        final Predicate1<MetaSchema> schemaMatcher = namedMatcher(schemaPattern);
        final Predicate1<MetaColumn> columnMatcher =
                namedMatcher(columnNamePattern);
        try {
            return createResultSet(schemas(catalog)
                            .where(schemaMatcher)
                            .selectMany(
                                    new Function1<MetaSchema, Enumerable<MetaTable>>() {
                                        public Enumerable<MetaTable> apply(MetaSchema schema) {
                                            return tables(schema, tableNameMatcher);
                                        }
                                    })
                            .selectMany(
                                    new Function1<MetaTable, Enumerable<MetaColumn>>() {
                                        public Enumerable<MetaColumn> apply(MetaTable schema) {
                                            return columns(schema);
                                        }
                                    })
                            .where(columnMatcher),
                    MetaColumn.class,
                    "TABLE_CAT",
                    "TABLE_SCHEM",
                    "TABLE_NAME",
                    "COLUMN_NAME",
                    "DATA_TYPE",
                    "TYPE_NAME",
                    "COLUMN_SIZE",
                    "BUFFER_LENGTH",
                    "DECIMAL_DIGITS",
                    "NUM_PREC_RADIX",
                    "NULLABLE",
                    "REMARKS",
                    "COLUMN_DEF",
                    "SQL_DATA_TYPE",
                    "SQL_DATETIME_SUB",
                    "CHAR_OCTET_LENGTH",
                    "ORDINAL_POSITION",
                    "IS_NULLABLE",
                    "SCOPE_CATALOG",
                    "SCOPE_SCHEMA",
                    "SCOPE_TABLE",
                    "SOURCE_DATA_TYPE",
                    "IS_AUTOINCREMENT",
                    "IS_GENERATEDCOLUMN");
        } catch (PrivacyException e) {
            e.printStackTrace();
            throw new RuntimeException(
                    "parse failed: " + e.getMessage(), e);
        }
    }

    Enumerable<MetaCatalog> catalogs() throws PrivacyException {
        return Linq4j.asEnumerable(
                CalciteSchema.from(getConnection().getRootSchema()).getSubSchemaMap().values())
                .select(
                        new Function1<CalciteSchema, MetaCatalog>() {
                            public MetaCatalog apply(CalciteSchema calciteSchema) {
                                return new MetaCatalog(calciteSchema.getName());
                            }
                        });
    }

    Enumerable<MetaTableType> tableTypes() {
        return Linq4j.asEnumerable(
                ImmutableList.of(
                        new MetaTableType("TABLE"), new MetaTableType("VIEW")));
    }

    Enumerable<MetaSchema> schemas(String catalog) throws PrivacyException {
        final Predicate1<MetaSchema> catalogMatcher = namedMatcher(Pat.of(catalog));
        return Linq4j.asEnumerable(
                CalciteSchema.from(getConnection().getRootSchema()).getSubSchemaMap().values())
                .select(
                        new Function1<CalciteSchema, MetaSchema>() {
                            public MetaSchema apply(CalciteSchema calciteSchema) {
                                return new QuarkMetaSchema(
                                        calciteSchema,
                                        null,
                                        calciteSchema.getName());
                            }
                        })
                .where(catalogMatcher)
                .selectMany(
                        new Function1<MetaSchema, Enumerable<MetaSchema>>() {
                            @Override
                            public Enumerable<MetaSchema> apply(MetaSchema metaSchema) {
                                final CalciteSchema schema = ((QuarkMetaSchema) metaSchema).calciteSchema;
                                return Linq4j.asEnumerable(schema.getSubSchemaMap().values())
                                        .select(
                                                new Function1<CalciteSchema, MetaSchema>() {
                                                    public MetaSchema apply(CalciteSchema calciteSchema) {
                                                        return new QuarkMetaSchema(
                                                                calciteSchema,
                                                                schema.getName(),
                                                                calciteSchema.getName());
                                                    }
                                                });
                            }
                        })
                .orderBy(
                        new Function1<MetaSchema, Comparable>() {
                            public Comparable apply(MetaSchema metaSchema) {
                                return (Comparable) FlatLists.of(
                                        Util.first(metaSchema.tableCatalog, ""),
                                        metaSchema.tableSchem);
                            }
                        });
    }

    Enumerable<MetaTable> tables(final MetaSchema schema_) {
        final QuarkMetaSchema schema = (QuarkMetaSchema) schema_;
        return Linq4j.asEnumerable(schema.calciteSchema.getTableNames())
                .select(
                        new Function1<String, MetaTable>() {
                            public MetaTable apply(String name) {
                                final Table table =
                                        schema.calciteSchema.getTable(name, true).getTable();
                                return new QuarkMetaTable(table,
                                        schema.tableCatalog,
                                        schema.tableSchem,
                                        name);
                            }
                        })
                .concat(
                        Linq4j.asEnumerable(
                                schema.calciteSchema.getTablesBasedOnNullaryFunctions()
                                        .entrySet())
                                .select(
                                        new Function1<Map.Entry<String, Table>, MetaTable>() {
                                            public MetaTable apply(Map.Entry<String, Table> pair) {
                                                final Table table = pair.getValue();
                                                return new QuarkMetaTable(table,
                                                        schema.tableCatalog,
                                                        schema.tableSchem,
                                                        pair.getKey());
                                            }
                                        }));
    }

    Enumerable<MetaTable> tables(
            final MetaSchema schema,
            final Predicate1<String> matcher) {
        return tables(schema)
                .where(
                        new Predicate1<MetaTable>() {
                            public boolean apply(MetaTable v1) {
                                return matcher.apply(v1.getName());
                            }
                        });
    }

    private ImmutableList<MetaTypeInfo> getAllDefaultType() {
        final ImmutableList.Builder<MetaTypeInfo> allTypeList =
                new ImmutableList.Builder<>();
        final RelDataTypeSystem typeSystem = getConnection().getTypeFactory().getTypeSystem();
        for (SqlTypeName sqlTypeName : SqlTypeName.values()) {
            allTypeList.add(
                    new MetaTypeInfo(sqlTypeName.getName(),
                            sqlTypeName.getJdbcOrdinal(),
                            typeSystem.getMaxPrecision(sqlTypeName),
                            typeSystem.getLiteral(sqlTypeName, true),
                            typeSystem.getLiteral(sqlTypeName, false),
                            // All types are nullable
                            (short) DatabaseMetaData.typeNullable,
                            typeSystem.isCaseSensitive(sqlTypeName),
                            // Making all type searchable; we may want to
                            // be specific and declare under SqlTypeName
                            (short) DatabaseMetaData.typeSearchable,
                            false,
                            false,
                            typeSystem.isAutoincrement(sqlTypeName),
                            (short) sqlTypeName.getMinScale(),
                            (short) typeSystem.getMaxScale(sqlTypeName),
                            typeSystem.getNumTypeRadix(sqlTypeName)));
        }
        return allTypeList.build();
    }

    protected Enumerable<MetaTypeInfo> allTypeInfo() {
        return Linq4j.asEnumerable(getAllDefaultType());
    }

    public Enumerable<MetaColumn> columns(final MetaTable table_) {
        final QuarkMetaTable table = (QuarkMetaTable) table_;
        final RelDataType rowType =
                table.calciteTable.getRowType(getConnection().typeFactory);
        return Linq4j.asEnumerable(rowType.getFieldList())
                .select(
                        new Function1<RelDataTypeField, MetaColumn>() {
                            public MetaColumn apply(RelDataTypeField field) {
                                final int precision =
                                        field.getType().getSqlTypeName().allowsPrec()
                                                && !(field.getType()
                                                instanceof RelDataTypeFactoryImpl.JavaType)
                                                ? field.getType().getPrecision()
                                                : -1;
                                return new MetaColumn(
                                        table.tableCat,
                                        table.tableSchem,
                                        table.tableName,
                                        field.getName(),
                                        field.getType().getSqlTypeName().getJdbcOrdinal(),
                                        field.getType().getFullTypeString(),
                                        precision,
                                        field.getType().getSqlTypeName().allowsScale()
                                                ? field.getType().getScale()
                                                : null,
                                        10,
                                        field.getType().isNullable()
                                                ? DatabaseMetaData.columnNullable
                                                : DatabaseMetaData.columnNoNulls,
                                        precision,
                                        field.getIndex() + 1,
                                        field.getType().isNullable() ? "YES" : "NO");
                            }
                        });
    }

    @Override
    public MetaResultSet getSchemas(ConnectionHandle ch, String catalog, Pat schemaPattern) {
        final Predicate1<MetaSchema> schemaMatcher = namedMatcher(schemaPattern);
        try {
            return createResultSet(schemas(catalog).where(schemaMatcher),
                    MetaSchema.class,
                    "TABLE_SCHEM",
                    "TABLE_CATALOG");
        } catch (PrivacyException e) {
            e.printStackTrace();
            throw new RuntimeException(
                    "parse failed: " + e.getMessage(), e);
        }
    }

    @Override
    public MetaResultSet getCatalogs(ConnectionHandle ch) {
        try {
            return createResultSet(catalogs(),
                    MetaCatalog.class,
                    "TABLE_CAT");
        } catch (PrivacyException e) {
            e.printStackTrace();
            throw new RuntimeException(
                    "parse failed: " + e.getMessage(), e);
        }
    }


    public MetaResultSet getTableTypes(ConnectionHandle ch) {
        return createResultSet(tableTypes(),
                MetaTableType.class,
                "TABLE_TYPE");
    }

//  @Override
//  public Iterable<Object> createIterable(StatementHandle handle, QueryState state,
//      Signature signature, List<TypedValue> parameterValues, Frame firstFrame) {
//    // Drop QueryState
//    return _createIterable(handle, signature, parameterValues, firstFrame);
//  }
//
//  Iterable<Object> _createIterable(StatementHandle handle,
//      Signature signature, List<TypedValue> parameterValues, Frame firstFrame) {
//    try {
//      //noinspection unchecked
//      final CalcitePrepare.CalciteSignature<Object> calciteSignature =
//          (CalcitePrepare.CalciteSignature<Object>) signature;
//      return getConnection().enumerable(handle, calciteSignature);
//    } catch (SQLException e) {
//      throw new RuntimeException(e.getMessage());
//    }
//  }

    @Override
    public Frame fetch(StatementHandle h, long offset, int fetchMaxRowCount) {
        final PrivacyConnectionImpl calciteConnection = getConnection();
        PrivacyJdbcStatement stmt = calciteConnection.server.getStatement(h);
        final Signature signature = stmt.getSignature();
        final Iterator<Object> iterator;
        if (stmt.getResultSet() == null) {
            final Iterable<Object> iterable =
                    Linq4j.emptyEnumerable();
            iterator = iterable.iterator();
            stmt.setResultSet(iterator);
        } else {
            iterator = stmt.getResultSet();
        }
        final List<List<Object>> list = new ArrayList<>();
        List<List<Object>> rows =
                MetaImpl.collect(signature.cursorFactory,
                        LimitIterator.of(iterator, fetchMaxRowCount), list);
        boolean done = fetchMaxRowCount == 0 || list.size() < fetchMaxRowCount;
        return new Meta.Frame(offset, done, (List<Object>) (List) rows);
    }

    @Override
    public ExecuteResult execute(StatementHandle h,
                                 List<TypedValue> parameterValues, long maxRowCount) {
        try {
            if (MetaImpl.checkParameterValueHasNull(parameterValues)) {
                throw new SQLException("exception while executing query: unbound parameter");
            }

            final StatementInfo statementInfo = Objects.requireNonNull(
                    statementCache.getIfPresent(h.id),
                    "Statement not found, potentially expired. " + h);
            final List<MetaResultSet> resultSets = new ArrayList<>();
            final PreparedStatement preparedStatement =
                    (PreparedStatement) statementInfo.statement;

            if (parameterValues != null) {
                for (int i = 0; i < parameterValues.size(); i++) {
                    TypedValue o = parameterValues.get(i);
                    preparedStatement.setObject(i + 1, o.toJdbc(calendar));
                }
            }

            if (preparedStatement.execute()) {
                final Meta.Frame frame;
                final Signature signature2;
                if (preparedStatement.isWrapperFor(AvaticaPreparedStatement.class)) {
                    signature2 = h.signature;
                } else {
                    h.signature = signature(preparedStatement.getMetaData(),
                            preparedStatement.getParameterMetaData(), h.signature.sql,
                            Meta.StatementType.SELECT);
                    signature2 = h.signature;
                }

                statementInfo.resultSet = preparedStatement.getResultSet();
                if (statementInfo.resultSet == null) {
                    frame = Frame.EMPTY;
                    resultSets.add(PrivacyMetaResultSet.empty(h.connectionId, h.id, signature2));
                } else {
                    resultSets.add(
                            PrivacyMetaResultSet.create(h.connectionId, h.id,
                                    statementInfo.resultSet, maxRowCount, signature2));
                }
            } else {
                resultSets.add(
                        PrivacyMetaResultSet.count(
                                h.connectionId, h.id, preparedStatement.getUpdateCount()));
            }

            return new ExecuteResult(resultSets);
        } catch (SQLException e) {
            throw propagate(e);
        }
    }

    @Override
    public ExecuteResult execute(StatementHandle statementHandle,
                                 List<TypedValue> list,
                                 int i)
            throws NoSuchStatementException {
        return null;
    }

//  @Override
//  public ExecuteResult execute(StatementHandle h,
//      List<TypedValue> parameterValues, long maxRowCount) {
//    final QuarkConnectionImpl calciteConnection = getConnection();
//    QuarkJdbcStatement stmt = calciteConnection.server.getStatement(h);
//    final Signature signature = stmt.getSignature();
//
//    MetaResultSet metaResultSet;
//    if (signature.statementType.canUpdate()) {
//      final Iterable<Object> iterable =
//          _createIterable(h, signature, parameterValues, null);
//      final Iterator<Object> iterator = iterable.iterator();
//      stmt.setResultSet(iterator);
//      metaResultSet = MetaResultSet.count(h.connectionId, h.id,
//          ((Number) iterator.next()).intValue());
//    } else {
//      // Don't populate the first frame.
//      // It's not worth saving a round-trip, since we're local.
//      final Meta.Frame frame =
//          new Meta.Frame(0, false, Collections.emptyList());
//      metaResultSet =
//          MetaResultSet.create(h.connectionId, h.id, false, signature, frame);
//    }
//
//    return new ExecuteResult(ImmutableList.of(metaResultSet));
//  }

    public boolean syncResults(StatementHandle h, QueryState state, long offset)
            throws NoSuchStatementException {
        // Doesn't have application in Calcite itself.
        throw new UnsupportedOperationException();
    }

    @Override public void commit(ConnectionHandle ch) {
    }

    @Override public void rollback(ConnectionHandle ch) {
    }

    /**
     * Metadata describing a Calcite schema.
     */
    private static class QuarkMetaSchema extends MetaSchema {
        private final CalciteSchema calciteSchema;

        QuarkMetaSchema(CalciteSchema calciteSchema,
                        String tableCatalog, String tableSchem) {
            super(tableCatalog, tableSchem);
            this.calciteSchema = calciteSchema;
        }
    }

    /**
     * Metadata describing a Calcite table.
     */
    private static class QuarkMetaTable extends MetaTable {
        private final Table calciteTable;

        QuarkMetaTable(Table calciteTable, String tableCat,
                       String tableSchem, String tableName) {
            super(tableCat, tableSchem, tableName,
                    calciteTable.getJdbcTableType().name());
            this.calciteTable = Preconditions.checkNotNull(calciteTable);
        }
    }

    /**
     * Converts from JDBC metadata to Avatica columns.
     */
    protected static List<ColumnMetaData> columns(ResultSetMetaData metaData)
            throws SQLException {
        if (metaData == null) {
            return Collections.emptyList();
        }
        final List<ColumnMetaData> columns = new ArrayList<>();
        for (int i = 1; i <= metaData.getColumnCount(); i++) {
            final SqlType sqlType = SqlType.valueOf(metaData.getColumnType(i));
            final ColumnMetaData.Rep rep = ColumnMetaData.Rep.of(sqlType.internal);
            final ColumnMetaData.AvaticaType t;
            if (sqlType == SqlType.ARRAY || sqlType == SqlType.STRUCT || sqlType == SqlType.MULTISET) {
                ColumnMetaData.AvaticaType arrayValueType = ColumnMetaData.scalar(Types.JAVA_OBJECT,
                        metaData.getColumnTypeName(i), ColumnMetaData.Rep.OBJECT);
                t = ColumnMetaData.array(arrayValueType, metaData.getColumnTypeName(i), rep);
            } else {
                t = ColumnMetaData.scalar(metaData.getColumnType(i), metaData.getColumnTypeName(i), rep);
            }
            ColumnMetaData md =
                    new ColumnMetaData(i - 1, metaData.isAutoIncrement(i),
                            metaData.isCaseSensitive(i), metaData.isSearchable(i),
                            metaData.isCurrency(i), metaData.isNullable(i),
                            metaData.isSigned(i), metaData.getColumnDisplaySize(i),
                            metaData.getColumnLabel(i), metaData.getColumnName(i),
                            metaData.getSchemaName(i), metaData.getPrecision(i),
                            metaData.getScale(i), metaData.getTableName(i),
                            metaData.getCatalogName(i), t, metaData.isReadOnly(i),
                            metaData.isWritable(i), metaData.isDefinitelyWritable(i),
                            metaData.getColumnClassName(i));
            columns.add(md);
        }
        return columns;
    }

    /**
     * Converts from JDBC metadata to Avatica parameters
     */
    protected static List<AvaticaParameter> parameters(ParameterMetaData metaData)
            throws SQLException {
        if (metaData == null) {
            return Collections.emptyList();
        }
        final List<AvaticaParameter> params = new ArrayList<>();
        for (int i = 1; i <= metaData.getParameterCount(); i++) {
            params.add(
                    new AvaticaParameter(metaData.isSigned(i), metaData.getPrecision(i),
                            metaData.getScale(i), metaData.getParameterType(i),
                            metaData.getParameterTypeName(i),
                            metaData.getParameterClassName(i), "?" + i));
        }
        return params;
    }

    protected static Signature signature(ResultSetMetaData metaData,
                                         ParameterMetaData parameterMetaData, String sql,
                                         Meta.StatementType statementType) throws SQLException {
        final CursorFactory cf = CursorFactory.ARRAY;  // because JdbcResultSet#frame
        return new Signature(columns(metaData), sql, parameters(parameterMetaData),
                null, cf, statementType);
    }

    protected static Signature signature(ResultSetMetaData metaData)
            throws SQLException {
        return signature(metaData, null, null, null);
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

    /**
     * Configurable connection cache settings.
     */
    public enum ConnectionCacheSettings {
        /**
         * JDBC connection property for setting connection cache concurrency level.
         */
        CONCURRENCY_LEVEL(CONN_CACHE_KEY_BASE + ".concurrency", "10"),

        /**
         * JDBC connection property for setting connection cache initial capacity.
         */
        INITIAL_CAPACITY(CONN_CACHE_KEY_BASE + ".initialcapacity", "100"),

        /**
         * JDBC connection property for setting connection cache maximum capacity.
         */
        MAX_CAPACITY(CONN_CACHE_KEY_BASE + ".maxcapacity", "1000"),

        /**
         * JDBC connection property for setting connection cache expiration duration.
         */
        EXPIRY_DURATION(CONN_CACHE_KEY_BASE + ".expiryduration", "10"),

        /**
         * JDBC connection property for setting connection cache expiration unit.
         */
        EXPIRY_UNIT(CONN_CACHE_KEY_BASE + ".expiryunit", TimeUnit.MINUTES.name());

        private final String key;
        private final String defaultValue;

        ConnectionCacheSettings(String key, String defaultValue) {
            this.key = key;
            this.defaultValue = defaultValue;
        }
    }

    /**
     * Configurable statement cache settings.
     */
    public enum StatementCacheSettings {
        /**
         * JDBC connection property for setting connection cache concurrency level.
         */
        CONCURRENCY_LEVEL(STMT_CACHE_KEY_BASE + ".concurrency", "100"),

        /**
         * JDBC connection property for setting connection cache initial capacity.
         */
        INITIAL_CAPACITY(STMT_CACHE_KEY_BASE + ".initialcapacity", "1000"),

        /**
         * JDBC connection property for setting connection cache maximum capacity.
         */
        MAX_CAPACITY(STMT_CACHE_KEY_BASE + ".maxcapacity", "10000"),

        /**
         * JDBC connection property for setting connection cache expiration duration.
         * <p>Used in conjunction with {@link #EXPIRY_UNIT}.</p>
         */
        EXPIRY_DURATION(STMT_CACHE_KEY_BASE + ".expirydiration", "5"),

        /**
         * JDBC connection property for setting connection cache expiration unit.
         * <p>Used in conjunction with {@link #EXPIRY_DURATION}.</p>
         */
        EXPIRY_UNIT(STMT_CACHE_KEY_BASE + ".expiryunit", TimeUnit.MINUTES.name());

        private final String key;
        private final String defaultValue;

        StatementCacheSettings(String key, String defaultValue) {
            this.key = key;
            this.defaultValue = defaultValue;
        }

        /**
         * The configuration key for specifying this setting.
         */
        public String key() {
            return key;
        }

        /**
         * The default value for this setting.
         */
        public String defaultValue() {
            return defaultValue;
        }
    }

    /**
     * Callback for {@link #connectionCache} member expiration.
     */
    private class ConnectionExpiryHandler
            implements RemovalListener<String, Connection> {

        public void onRemoval(RemovalNotification<String, Connection> notification) {
            String connectionId = notification.getKey();
            Connection doomed = notification.getValue();
            if (LOG.isDebugEnabled()) {
                LOG.debug("Expiring connection " + connectionId + " because "
                        + notification.getCause());
            }
            try {
                if (doomed != null) {
                    doomed.close();
                }
            } catch (Throwable t) {
                LOG.info("Exception thrown while expiring connection " + connectionId, t);
            }
        }
    }

    /**
     * Callback for {@link #statementCache} member expiration.
     */
    private class StatementExpiryHandler
            implements RemovalListener<Integer, StatementInfo> {
        public void onRemoval(RemovalNotification<Integer, StatementInfo> notification) {
            Integer stmtId = notification.getKey();
            StatementInfo doomed = notification.getValue();
            if (doomed == null) {
                // log/throw?
                return;
            }
            if (LOG.isDebugEnabled()) {
                LOG.debug("Expiring statement " + stmtId + " because "
                        + notification.getCause());
            }
            try {
                if (doomed.resultSet != null) {
                    doomed.resultSet.close();
                }
                if (doomed.statement != null) {
                    doomed.statement.close();
                }
            } catch (Throwable t) {
                LOG.info("Exception thrown while expiring statement " + stmtId);
            }
        }
    }

    /**
     * All we know about a statement.
     */
    private static class StatementInfo {
        final Statement statement; // sometimes a PreparedStatement
        ResultSet resultSet;

        private StatementInfo(Statement statement) {
            this.statement = Objects.requireNonNull(statement);
        }
    }

    /** Iterator that returns at most {@code limit} rows from an underlying
     * {@link Iterator}
     * @param <E>  Undelying type of objects of Iterator */
    private static class LimitIterator<E> implements Iterator<E> {
        private final Iterator<E> iterator;
        private final long limit;
        int i = 0;

        private LimitIterator(Iterator<E> iterator, long limit) {
            this.iterator = iterator;
            this.limit = limit;
        }

        static <E> Iterator<E> of(Iterator<E> iterator, long limit) {
            if (limit <= 0) {
                return iterator;
            }
            return new LimitIterator<>(iterator, limit);
        }

        public boolean hasNext() {
            return iterator.hasNext() && i < limit;
        }

        public E next() {
            ++i;
            return iterator.next();
        }

        public void remove() {
            throw new UnsupportedOperationException();
        }
    }
}
