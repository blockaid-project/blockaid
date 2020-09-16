package execution;

import org.apache.calcite.sql.SqlKind;

import com.google.common.cache.Cache;
import sql.ParserFactory;

import java.sql.Connection;
import java.util.Properties;

/**
 * Created by adeshr on 5/24/16.
 */
public class PrivacyExecutorFactory {
    private PrivacyExecutorFactory() {
    }

    public static PrivacyExecutor getPrivacyExecutor(SqlKind sqlKind,
                                                 ParserFactory parserFactory,
                                                 Properties info,
                                                 Cache<String, Connection> connectionCache) {
        if (sqlKind.equals(SqlKind.OTHER_DDL)) {
            //return new PrivacyDDLExecutor(parserFactory, info);
            return null;
        } else if (sqlKind.belongsTo(SqlKind.QUERY)) {
            return new PrivacyQueryExecutor(connectionCache);
        } else if (sqlKind.belongsTo(SqlKind.DML)){
            return new PrivacyDMLExecutor(connectionCache);
        }
        else {
            throw new UnsupportedOperationException("Cannot execute parsed Sql of kind: "
                    + sqlKind);
        }
    }
}
