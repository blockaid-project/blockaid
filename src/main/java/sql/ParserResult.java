package sql;

import org.apache.calcite.rel.RelNode;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;

/**
 * Created by amoghm on 3/4/16.
 */
public abstract class ParserResult {

    protected final String parsedSql;
    protected SqlKind kind;
    protected boolean isCheckable;
    protected final SqlNode sqlNode;
    protected final boolean parseResult;

    public ParserResult(String parsedSql, SqlKind kind,
                        SqlNode sqlNode,
                        boolean isCheckable,
                        boolean parseResult) {
        this.parsedSql = parsedSql;
        this.isCheckable = isCheckable;
        this.kind = kind;
        this.sqlNode = sqlNode;
        this.parseResult = parseResult;
    }

    public boolean getIsCheckable() {return isCheckable;}

    public String getParsedSql() {
        return parsedSql;
    }

    public SqlKind getKind() {
        return kind;
    }

    public SqlNode getSqlNode() {
        return sqlNode;
    }

    public boolean isParseResult() {
        return parseResult;
    }
}