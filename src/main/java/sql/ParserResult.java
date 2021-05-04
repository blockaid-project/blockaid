package sql;

import org.apache.calcite.rel.RelNode;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;

import java.util.Objects;

/**
 * Created by amoghm on 3/4/16.
 */
public abstract class ParserResult {

    protected String parsedSql;
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
        return parsedSql.replace("\n", " ");
    }

    // FIXME(zhangwen): HACK-- for replacing unnamed parameters with named parameters in the query string.
    public void setParsedSql(String s) {
        parsedSql = s;
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

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ParserResult that = (ParserResult) o;
        return Objects.equals(parsedSql, that.parsedSql);
    }

    @Override
    public int hashCode() {
        return Objects.hash(parsedSql);
    }
}