package sql;

import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;

/**
 * Created by amoghm on 3/4/16.
 *
 */
public class DDLParser implements Parser {
    public DDLParserResult parse(String sql) {
        return new DDLParserResult(sql,
                SqlKind.OTHER_DDL, null, true, true);
    }

    public boolean isCheckable(SqlNode sqlNode){
        return true;
    }

    /**
     * Parser Result for DDL statements
     */
    public class DDLParserResult extends ParserResult {
        public DDLParserResult(String parsedSql, SqlKind kind,
                               SqlNode sqlNode, boolean isCheckable, boolean parseResult) {
            super(parsedSql, kind, sqlNode, isCheckable, parseResult);
        }
    }
}