package fatjdbc.impl;

import fatjdbc.PrivacyConnection;
import fatjdbc.PrivacyJdbcStatement;
import org.apache.calcite.avatica.Meta;

import com.google.common.collect.Maps;

import fatjdbc.PrivacyConnectionImpl;

import java.util.Map;

/**
 * Implementation of Server.
 */
public class PrivacyServer {
    final Map<Integer, PrivacyJdbcStatement> statementMap = Maps.newHashMap();

    public void removeStatement(Meta.StatementHandle h) {
        statementMap.remove(h.id);
    }

    public void addStatement(PrivacyConnection connection,
                             Meta.StatementHandle h) {
        final PrivacyConnectionImpl c = (PrivacyConnectionImpl) connection;
        statementMap.put(h.id, new PrivacyJdbcStatementImpl(c));
    }

    public PrivacyJdbcStatement getStatement(Meta.StatementHandle h) {
        return statementMap.get(h.id);
    }
}