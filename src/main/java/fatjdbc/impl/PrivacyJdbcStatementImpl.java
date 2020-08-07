package fatjdbc.impl;

import fatjdbc.PrivacyConnection;
import org.apache.calcite.avatica.Meta;
import org.apache.calcite.server.CalciteServerStatement;

import com.google.common.base.Preconditions;

import fatjdbc.PrivacyConnectionImpl;
import fatjdbc.PrivacyJdbcStatement;

import java.util.Iterator;

/**
 * Implementation of {@link CalciteServerStatement}.
 */
public class PrivacyJdbcStatementImpl
        implements PrivacyJdbcStatement {
    private final PrivacyConnectionImpl connection;
    private Iterator<Object> iterator;
    private Meta.Signature signature;

    public PrivacyJdbcStatementImpl(PrivacyConnectionImpl connection) {
        this.connection = Preconditions.checkNotNull(connection);
    }

    public PrivacyConnection getConnection() {
        return connection;
    }

    public void setSignature(Meta.Signature signature) {
        this.signature = signature;
    }

    public Meta.Signature getSignature() {
        return signature;
    }

    public Iterator<Object> getResultSet() {
        return iterator;
    }

    public void setResultSet(Iterator<Object> iterator) {
        this.iterator = iterator;
    }
}