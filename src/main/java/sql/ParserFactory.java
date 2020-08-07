package sql;

import org.apache.calcite.avatica.util.Casing;
import org.apache.calcite.avatica.util.Quoting;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;

import sql.PrivacyException;

import java.sql.SQLException;
import java.util.Properties;

/**
 * Created by adeshr on 5/24/16.
 */
public class ParserFactory {
    private SqlQueryParser sqlQueryParser;
    private boolean reloadCache;

    public ParserFactory(Properties info) throws SQLException {
        sqlQueryParser = getSqlQueryParser(info);
        reloadCache = false;
    }

    public void setReloadCache() {
        this.reloadCache = true;
    }

    public void clearReloadCache() {
        this.reloadCache = false;
    }

    public SqlQueryParser getSqlQueryParser(Properties info)
            throws SQLException {
        if (reloadCache || sqlQueryParser == null) {
            try {
                sqlQueryParser = new SqlQueryParser(info);
                clearReloadCache();
            } catch (PrivacyException e) {
                throw new SQLException(e.getMessage(), e);
            }
        }
        return sqlQueryParser;
    }

    public Parser getParser(String sql, Properties info)
            throws SQLException {
        SqlParser parser = SqlParser.create(sql,
                SqlParser.configBuilder()
                        .setQuotedCasing(Casing.UNCHANGED)
                        .setUnquotedCasing(Casing.UNCHANGED)
                        .setQuoting(Quoting.DOUBLE_QUOTE)
                        //.setParserFactory(PrivacyParserImpl.FACTORY)
                        .build());
        SqlNode sqlNode;
        try {
            sqlNode = parser.parseStmt();
        } catch (SqlParseException e) {
            throw new RuntimeException(
                    "parse failed: " + e.getMessage(), e);
        }
        if (sqlNode.getKind().equals(SqlKind.OTHER_DDL)) {
            return new DDLParser();
        } else  {
            return getSqlQueryParser(info);
        }
    }
}
