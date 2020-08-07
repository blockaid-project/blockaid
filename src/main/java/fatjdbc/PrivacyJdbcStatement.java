package fatjdbc;

import org.apache.calcite.avatica.Meta;

import java.util.Iterator;

/**
 * Statement within a Quark JDBC Driver.
 */
public interface PrivacyJdbcStatement {
    /**
     * Returns the connection.
     */
    PrivacyConnection getConnection();

    void setSignature(Meta.Signature signature);

    Meta.Signature getSignature();

    Iterator<Object> getResultSet();

    void setResultSet(Iterator<Object> resultSet);
}
