package fatjdbc;

import org.apache.calcite.avatica.AvaticaStatement;
import org.apache.calcite.avatica.ColumnMetaData;
import org.apache.calcite.avatica.Meta;
import org.apache.calcite.avatica.util.DateTimeUtils;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.sql.Array;
import java.sql.Date;
import java.sql.ResultSet;
import java.sql.ResultSetMetaData;
import java.sql.SQLException;
import java.sql.Struct;
import java.sql.Time;
import java.sql.Timestamp;
import java.sql.Types;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.TreeMap;

/**
 * Implementation of {@link org.apache.calcite.avatica.Meta.MetaResultSet}
 * upon a JDBC {@link java.sql.ResultSet}.
 *
 * @see PrivacyMetaImpl
 */
public class PrivacyMetaResultSet extends Meta.MetaResultSet {
    protected static final Logger LOG = LoggerFactory.getLogger(PrivacyMetaResultSet.class);
    protected PrivacyMetaResultSet(String connectionId,
                                 int statementId,
                                 boolean ownStatement,
                                 Meta.Signature signature,
                                 Meta.Frame firstFrame) {
        this(connectionId, statementId, ownStatement, signature, firstFrame, -1L);
    }

    protected PrivacyMetaResultSet(String connectionId,
                                 int statementId,
                                 boolean ownStatement,
                                 Meta.Signature signature,
                                 Meta.Frame firstFrame,
                                 long updateCount) {
        super(connectionId, statementId, ownStatement, signature, firstFrame, updateCount);
    }

    /**
     * Creates a result set.
     */
    public static PrivacyMetaResultSet create(String connectionId, int statementId,
                                            ResultSet resultSet) {
        // -1 still limits to 100 but -2 does not limit to any number
        return create(connectionId, statementId, resultSet,
                PrivacyMetaImpl.UNLIMITED_COUNT);
    }

    /**
     * Creates a result set with maxRowCount.
     * If {@code maxRowCount} is -2 ({@link PrivacyMetaImpl#UNLIMITED_COUNT}),
     * returns an unlimited number of rows in a single frame; any other
     * negative value (typically -1) returns an unlimited number of rows
     * in frames of the default frame size.
     */
    public static PrivacyMetaResultSet create(String connectionId, int statementId,
                                            ResultSet resultSet, long maxRowCount) {
        try {
            Meta.Signature sig = PrivacyMetaImpl.signature(resultSet.getMetaData());
            return create(connectionId, statementId, resultSet, maxRowCount, sig);
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    public static PrivacyMetaResultSet create(String connectionId, int statementId,
                                            Iterator iterator,
                                            long maxRowCount, Meta.Signature signature) {
        try {
            final Calendar calendar = Calendar.getInstance(DateTimeUtils.GMT_ZONE);
            final int fetchRowCount;
            if (maxRowCount == PrivacyMetaImpl.UNLIMITED_COUNT) {
                fetchRowCount = -1;
            } else if (maxRowCount < 0L) {
                fetchRowCount = AvaticaStatement.DEFAULT_FETCH_SIZE;
            } else if (maxRowCount > AvaticaStatement.DEFAULT_FETCH_SIZE) {
                fetchRowCount = AvaticaStatement.DEFAULT_FETCH_SIZE;
            } else {
                fetchRowCount = (int) maxRowCount;
            }
            final Meta.Frame firstFrame;
            if (!iterator.hasNext()) {
                firstFrame = Meta.Frame.EMPTY;
            } else {
                firstFrame = frame(iterator, signature.columns, 0, fetchRowCount, calendar);
            }
            return new PrivacyMetaResultSet(connectionId, statementId, true, signature,
                    firstFrame);
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    public static PrivacyMetaResultSet create(String connectionId, int statementId,
                                            ResultSet resultSet,
                                            long maxRowCount, Meta.Signature signature) {
        try {
            final Calendar calendar = Calendar.getInstance(DateTimeUtils.GMT_ZONE);
            final int fetchRowCount;
            if (maxRowCount == PrivacyMetaImpl.UNLIMITED_COUNT) {
                fetchRowCount = -1;
            } else if (maxRowCount < 0L) {
                fetchRowCount = AvaticaStatement.DEFAULT_FETCH_SIZE;
            } else if (maxRowCount > AvaticaStatement.DEFAULT_FETCH_SIZE) {
                fetchRowCount = AvaticaStatement.DEFAULT_FETCH_SIZE;
            } else {
                fetchRowCount = (int) maxRowCount;
            }
            final Meta.Frame firstFrame = frame(resultSet, 0, fetchRowCount, calendar);
            if (firstFrame.done) {
                resultSet.close();
            }
            return new PrivacyMetaResultSet(connectionId, statementId, true, signature,
                    firstFrame);
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Creates a empty result set with empty frame
     */
    public static PrivacyMetaResultSet empty(String connectionId, int statementId,
                                           Meta.Signature signature) {
        return new PrivacyMetaResultSet(connectionId, statementId, true, signature,
                Meta.Frame.EMPTY);
    }

    /**
     * Creates a result set that only has an update count.
     */
    public static PrivacyMetaResultSet count(String connectionId, int statementId,
                                           int updateCount) {
        return new PrivacyMetaResultSet(connectionId, statementId, true, null, null, updateCount);
    }

    /**
     * Creates a frame containing a given number or unlimited number of rows
     * from a result set.
     */
    static Meta.Frame frame(ResultSet resultSet, long offset,
                            int fetchMaxRowCount, Calendar calendar) throws SQLException {
        final ResultSetMetaData metaData = resultSet.getMetaData();
        final int columnCount = metaData.getColumnCount();
        final int[] types = new int[columnCount];
        for (int i = 0; i < types.length; i++) {
            types[i] = metaData.getColumnType(i + 1);
        }
        final List<Object> rows = new ArrayList<>();
        // Meta prepare/prepareAndExecute 0 return 0 row and done
        boolean done = fetchMaxRowCount == 0;
        for (int i = 0; fetchMaxRowCount < 0 || i < fetchMaxRowCount; i++) {
            if (!resultSet.next()) {
                done = true;
                resultSet.close();
                break;
            }
            Object[] columns = new Object[columnCount];
            for (int j = 0; j < columnCount; j++) {
                columns[j] = getValue(resultSet, types[j], j, calendar);
            }
            rows.add(columns);
        }
        return new Meta.Frame(offset, done, rows);
    }

    /**
     * Creates a frame containing a given number or unlimited number of rows
     * from an Iterator.
     */
    static Meta.Frame frame(Iterator iterator,
                            List<ColumnMetaData> columnMetaDatas,
                            long offset,
                            int fetchMaxRowCount,
                            Calendar calendar) throws SQLException {
        final int columnCount = columnMetaDatas.size();
        final int[] types = new int[columnCount];
        for (int i = 0; i < types.length; i++) {
            types[i] = columnMetaDatas.get(i).type.id;
        }
        final List<Object> rows = new ArrayList<>();
        // Meta prepare/prepareAndExecute 0 return 0 row and done
        boolean done = fetchMaxRowCount == 0;
        for (int i = 0; fetchMaxRowCount < 0 || i < fetchMaxRowCount; i++) {
            if (!iterator.hasNext()) {
                done = true;
                break;
            }

            Object values = iterator.next();
            Object[] columns = new Object[columnCount];

            if (columnCount == 1 && !values.getClass().isArray()) {
                columns[0] = getValue(values, types[0], 0, calendar);
            } else if (values != null && values instanceof Collection) {
                Iterator valueIterator = ((Collection) values).iterator();
                for (int j = 0; j < columnCount; j++) {
                    columns[j] = getValue(valueIterator.next(), types[j], j, calendar);
                }
            } else {
                Object[] arrayValues = (Object[]) values;
                for (int j = 0; j < columnCount; j++) {
                    columns[j] =
                            getValue(arrayValues[j], types[j], j, calendar);
                }
            }
            rows.add(columns);
        }
        return new Meta.Frame(offset, done, rows);
    }

    private static Object getValue(Object obj, int type, int j,
                                   Calendar calendar) throws SQLException {
        if (obj == null) {
            return null;
        }
        // Hack for QuboleDB
        // returns every null value as String of value null
        if (obj instanceof String
                && ((String) obj).equalsIgnoreCase("null")) {
            return null;
        }

        switch (type) {
            case Types.BIGINT:
                if (obj instanceof String) {
                    return Long.valueOf((String) obj);
                }
                return obj;
            case Types.INTEGER:
                if (obj instanceof String) {
                    return Integer.valueOf((String) obj);
                }
                return obj;
            case Types.SMALLINT:
                if (obj instanceof String) {
                    return Short.valueOf((String) obj);
                }
                return obj;
            case Types.TINYINT:
                if (obj instanceof String) {
                    return Byte.valueOf((String) obj);
                }
                return obj;
            case Types.DOUBLE:
            case Types.FLOAT:
                if (obj instanceof String) {
                    return Double.valueOf((String) obj);
                }
                return obj;
            case Types.REAL:
                if (obj instanceof String) {
                    return Float.valueOf((String) obj);
                }
                return obj;
            case Types.DATE:
                if (obj instanceof String) {
                    return Date.valueOf((String) obj);
                }
                return obj;
            case Types.TIME:
                if (obj instanceof String) {
                    return Time.valueOf((String) obj);
                }
                return obj;
            case Types.TIMESTAMP:
                if (obj instanceof String) {
                    return Timestamp.valueOf((String) obj);
                }
                return obj;
            case Types.ARRAY:
                final Array array = (Array) obj;
                if (null == array) {
                    return null;
                }
                ResultSet arrayValues = array.getResultSet();
                TreeMap<Integer, Object> map = new TreeMap<>();
                while (arrayValues.next()) {
                    // column 1 is the index in the array, column 2 is the value.
                    // Recurse on `getValue` to unwrap nested types correctly.
                    // `j` is zero-indexed and incremented for us, thus we have `1` being used twice.
                    map.put(arrayValues.getInt(1), getValue(arrayValues, array.getBaseType(), 1, calendar));
                }
                // If the result set is not in the same order as the actual Array, TreeMap fixes that.
                // Need to make a concrete list to ensure Jackson serialization.
                //return new ListLike<Object>(new ArrayList<>(map.values()), ListLikeType.ARRAY);
                return new ArrayList<>(map.values());
            case Types.STRUCT:
                Struct struct = (Struct) obj;
                Object[] attrs = struct.getAttributes();
                List<Object> list = new ArrayList<>(attrs.length);
                for (Object o : attrs) {
                    list.add(o);
                }
                return list;
            default:
                return obj;
        }
    }

    private static Object getValue(ResultSet resultSet, int type, int j,
                                   Calendar calendar) throws SQLException {
        switch (type) {
            case Types.BIGINT:
                final long aLong = resultSet.getLong(j + 1);
                return aLong == 0 && resultSet.wasNull() ? null : aLong;
            case Types.INTEGER:
                final int anInt = resultSet.getInt(j + 1);
                return anInt == 0 && resultSet.wasNull() ? null : anInt;
            case Types.SMALLINT:
                final short aShort = resultSet.getShort(j + 1);
                return aShort == 0 && resultSet.wasNull() ? null : aShort;
            case Types.TINYINT:
                final byte aByte = resultSet.getByte(j + 1);
                return aByte == 0 && resultSet.wasNull() ? null : aByte;
            case Types.DOUBLE:
            case Types.FLOAT:
                final double aDouble = resultSet.getDouble(j + 1);
                return aDouble == 0D && resultSet.wasNull() ? null : aDouble;
            case Types.REAL:
                final float aFloat = resultSet.getFloat(j + 1);
                return aFloat == 0D && resultSet.wasNull() ? null : aFloat;
            case Types.DATE:
                final Date aDate = resultSet.getDate(j + 1, calendar);
                return aDate == null
                        ? null
                        : (int) (aDate.getTime() / DateTimeUtils.MILLIS_PER_DAY);
            case Types.TIME:
                final Time aTime = resultSet.getTime(j + 1, calendar);
                return aTime == null
                        ? null
                        : (int) (aTime.getTime() % DateTimeUtils.MILLIS_PER_DAY);
            case Types.TIMESTAMP:
                final Timestamp aTimestamp = resultSet.getTimestamp(j + 1, calendar);
                return aTimestamp == null ? null : aTimestamp.getTime();
            case Types.ARRAY:
                final Array array = resultSet.getArray(j + 1);
                if (null == array) {
                    return null;
                }
                ResultSet arrayValues = array.getResultSet();
                TreeMap<Integer, Object> map = new TreeMap<>();
                while (arrayValues.next()) {
                    // column 1 is the index in the array, column 2 is the value.
                    // Recurse on `getValue` to unwrap nested types correctly.
                    // `j` is zero-indexed and incremented for us, thus we have `1` being used twice.
                    map.put(arrayValues.getInt(1), getValue(arrayValues, array.getBaseType(), 1, calendar));
                }
                // If the result set is not in the same order as the actual Array, TreeMap fixes that.
                // Need to make a concrete list to ensure Jackson serialization.
                //return new ListLike<Object>(new ArrayList<>(map.values()), ListLikeType.ARRAY);
                return new ArrayList<>(map.values());
            case Types.STRUCT:
                Struct struct = resultSet.getObject(j + 1, Struct.class);
                Object[] attrs = struct.getAttributes();
                List<Object> list = new ArrayList<>(attrs.length);
                for (Object o : attrs) {
                    list.add(o);
                }
                return list;
            default:
                return resultSet.getObject(j + 1);
        }
    }
}
