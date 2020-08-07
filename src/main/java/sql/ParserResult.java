package sql;

import org.apache.calcite.rel.RelNode;
import org.apache.calcite.sql.SqlKind;

/**
 * Created by amoghm on 3/4/16.
 */
public abstract class ParserResult {
    protected final String parsedSql;
    protected SqlKind kind;

    protected final RelNode relNode;
    protected final boolean parseResult;
    public ParserResult(String parsedSql, SqlKind kind,
                        RelNode relNode, boolean parseResult) {
        this.parsedSql = parsedSql;
        this.kind = kind;
        this.relNode = relNode;
        this.parseResult = parseResult;
    }

    public String getParsedSql() {
        return parsedSql;
    }

    public SqlKind getKind() {
        return kind;
    }

    public RelNode getRelNode() {
        return relNode;
    }

    public boolean isParseResult() {
        return parseResult;
    }
}