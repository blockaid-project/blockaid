package sql;

import org.apache.calcite.rel.RelNode;
import org.apache.calcite.sql.SqlKind;

/**
 * Created by amoghm on 3/4/16.
 *
 * Parser for Quark's DDL Statements
 */
public class DDLParser implements Parser {
    public DDLParserResult parse(String sql) {
        return new DDLParserResult(sql,
                SqlKind.OTHER_DDL, null, true);
    }

    /**
     * Parser Result for DDL statements
     */
    public class DDLParserResult extends ParserResult {
        public DDLParserResult(String parsedSql, SqlKind kind,
                               RelNode relNode, boolean parseResult) {
            super(parsedSql, kind, relNode, parseResult);
        }
    }
}