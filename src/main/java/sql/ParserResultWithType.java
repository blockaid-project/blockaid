package sql;

import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.sql.SqlNode;

public class ParserResultWithType extends ParserResult {
    private final RelDataType type;

    public ParserResultWithType(SqlNode sqlNode, RelDataType type) {
        super(sqlNode);
        this.type = type;
    }

    public RelDataType getType() {
        return type;
    }
}
