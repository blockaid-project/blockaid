package sql;

import org.apache.calcite.rel.RelNode;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;

import java.util.Objects;

/**
 * Created by amoghm on 3/4/16.
 */
public class ParserResult {
    protected final SqlNode sqlNode;

    // Lazily computed (`node.toString` can take a while).  Use `getParsedSql()` to access.
    private String parsedSql = null;

    public ParserResult(SqlNode sqlNode) {
        this.sqlNode = sqlNode;
    }

    public String getParsedSql() {
        if (parsedSql == null) {
            parsedSql = sqlNode.toString().replace("\n", " ");
        }
        return parsedSql;
    }

    public SqlKind getKind() {
        return sqlNode.getKind();
    }

    public SqlNode getSqlNode() {
        return sqlNode;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ParserResult that = (ParserResult) o;
        return Objects.equals(getParsedSql(), that.getParsedSql());
    }

    @Override
    public int hashCode() {
        return Objects.hash(getParsedSql());
    }
}