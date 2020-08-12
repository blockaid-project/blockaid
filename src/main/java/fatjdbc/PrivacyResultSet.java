package fatjdbc;

import org.apache.calcite.avatica.AvaticaResultSet;
import org.apache.calcite.avatica.AvaticaResultSetMetaData;
import org.apache.calcite.avatica.AvaticaStatement;
import org.apache.calcite.avatica.ColumnMetaData;
import org.apache.calcite.avatica.Handler;
import org.apache.calcite.avatica.Meta;
import org.apache.calcite.avatica.util.Cursor;
import org.apache.calcite.jdbc.CalcitePrepare;
import org.apache.calcite.linq4j.Enumerator;
import org.apache.calcite.linq4j.Linq4j;
import org.apache.calcite.rel.RelCollation;
import org.apache.calcite.runtime.ArrayEnumeratorCursor;
import org.apache.calcite.runtime.ObjectEnumeratorCursor;

import com.google.common.collect.ImmutableList;

import java.sql.ResultSet;
import java.sql.ResultSetMetaData;
import java.sql.SQLException;
import java.util.List;
import java.util.TimeZone;

/**
 * Implementation of {@link ResultSet}
 * for the Quark engine.
 */
public class PrivacyResultSet extends AvaticaResultSet {
  PrivacyResultSet(AvaticaStatement statement,
                   Meta.Signature signature,
                   ResultSetMetaData resultSetMetaData, TimeZone timeZone,
                   Meta.Frame firstFrame) throws SQLException {
    super(statement, null, signature, resultSetMetaData, timeZone, firstFrame);
  }

  @Override
  protected fatjdbc.PrivacyResultSet execute() throws SQLException {
    // Call driver's callback. It is permitted to throw a RuntimeException.
    PrivacyConnectionImpl connection = getPrivacyConnection();
    final boolean autoTemp = connection.config().autoTemp();
    Handler.ResultSink resultSink = null;
    if (autoTemp) {
      resultSink = new Handler.ResultSink() {
        public void toBeCompleted() {
        }
      };
    }
    connection.getDriver().handler.onStatementExecute(statement, resultSink);

    super.execute();
    return this;
  }

  @Override
  public ResultSet create(ColumnMetaData.AvaticaType elementType,
                          Iterable<Object> iterable) throws SQLException {
    final List<ColumnMetaData> columnMetaDataList;
    if (elementType instanceof ColumnMetaData.StructType) {
      columnMetaDataList = ((ColumnMetaData.StructType) elementType).columns;
    } else {
      columnMetaDataList =
          ImmutableList.of(ColumnMetaData.dummy(elementType, false));
    }
    final CalcitePrepare.CalciteSignature signature =
        (CalcitePrepare.CalciteSignature) this.signature;
    final CalcitePrepare.CalciteSignature<Object> newSignature =
        new CalcitePrepare.CalciteSignature<>(signature.sql,
            signature.parameters, signature.internalParameters,
            signature.rowType, columnMetaDataList, Meta.CursorFactory.ARRAY,
            signature.rootSchema, ImmutableList.<RelCollation>of(), -1, null);
    ResultSetMetaData subResultSetMetaData =
        new AvaticaResultSetMetaData(statement, null, newSignature);
    final fatjdbc.PrivacyResultSet resultSet =
        new fatjdbc.PrivacyResultSet(statement, signature, subResultSetMetaData,
            localCalendar.getTimeZone(), new Meta.Frame(0, true, iterable));
    final Cursor cursor = resultSet.createCursor(elementType, iterable);
    return resultSet.execute2(cursor, columnMetaDataList);
  }

  private Cursor createCursor(ColumnMetaData.AvaticaType elementType,
                              Iterable iterable) {
    final Enumerator enumerator = Linq4j.iterableEnumerator(iterable);
    //noinspection unchecked
    return !(elementType instanceof ColumnMetaData.StructType)
        || ((ColumnMetaData.StructType) elementType).columns.size() == 1
        ? new ObjectEnumeratorCursor(enumerator)
        : new ArrayEnumeratorCursor(enumerator);
  }

  // do not make public
  PrivacyConnectionImpl getPrivacyConnection() throws SQLException {
    return (PrivacyConnectionImpl) statement.getConnection();
  }
}
