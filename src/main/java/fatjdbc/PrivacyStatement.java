package fatjdbc;

import org.apache.calcite.avatica.AvaticaResultSet;
import org.apache.calcite.avatica.AvaticaStatement;
import org.apache.calcite.avatica.Meta;

import java.sql.SQLException;

/**
 * Implementation of {@link java.sql.Statement}
 * for the Calcite engine.
 */
public abstract class PrivacyStatement extends AvaticaStatement {
    /**
     * Creates a QuarkStatement.
     *
     * @param connection           Connection
     * @param h                    Statement handle
     * @param resultSetType        Result set type
     * @param resultSetConcurrency Result set concurrency
     * @param resultSetHoldability Result set holdability
     */
    PrivacyStatement(PrivacyConnectionImpl connection, Meta.StatementHandle h,
                   int resultSetType, int resultSetConcurrency, int resultSetHoldability) {
        super(connection, h, resultSetType, resultSetConcurrency,
                resultSetHoldability);
    }

    // implement Statement

    @Override
    public <T> T unwrap(Class<T> iface) throws SQLException {
        if (iface == PrivacyJdbcStatement.class) {
            return iface.cast(getConnection().server.getStatement(handle));
        }
        return super.unwrap(iface);
    }

    @Override
    public PrivacyConnectionImpl getConnection() {
        return (PrivacyConnectionImpl) connection;
    }

    @Override
    protected void close_() {
        if (!closed) {
            closed = true;
            final PrivacyConnectionImpl connection1 =
                    (PrivacyConnectionImpl) connection;
            connection1.server.removeStatement(handle);
            if (openResultSet != null) {
                AvaticaResultSet c = openResultSet;
                openResultSet = null;
                c.close();
            }
            // If onStatementClose throws, this method will throw an exception (later
            // converted to SQLException), but this statement still gets closed.
            connection1.getDriver().handler.onStatementClose(this);
        }
    }
}