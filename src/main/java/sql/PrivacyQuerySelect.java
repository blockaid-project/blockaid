package sql;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.*;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;
import solver.PSJ;
import solver.Query;
import solver.Schema;
import solver.Tuple;

import java.util.*;

public class PrivacyQuerySelect extends PrivacyQuery {
    private ParsedPSJ parsedPSJ;

    public PrivacyQuerySelect(ParserResult parsedSql, SchemaPlusWithKey schema) {
        this(parsedSql, schema, new Object[0], Collections.emptyList());
    }

    public PrivacyQuerySelect(ParserResult parsedSql, SchemaPlusWithKey schema, Object[] parameters, List<String> paramNames) {
        super(parsedSql, parameters, paramNames);
        parsedPSJ = new ParsedPSJ(getSelectNode(parsedSql), schema, Arrays.asList(parameters), paramNames);
    }

    private SqlSelect getSelectNode(ParserResult result) {
        if (result.getSqlNode() instanceof SqlOrderBy) {
            return (SqlSelect) ((SqlOrderBy) result.getSqlNode()).query;
        } else {
            return (SqlSelect) result.getSqlNode();
        }
    }

    @Override
    public Set<String> getProjectColumns() {
        return new HashSet<>(parsedPSJ.getProjectColumns());
    }

    @Override
    public Set<String> getThetaColumns() {
        return new HashSet<>(parsedPSJ.getThetaColumns());
    }

    @Override
    public Query getSolverQuery(Schema schema) {
        return parsedPSJ.getSolverQuery(schema);
    }

    @Override
    public Query getSolverQuery(Schema schema, String prefix, int offset) {
        return parsedPSJ.getSolverQuery(schema, prefix, offset);
    }

    @Override
    public List<Boolean> getResultBitmap() {
        return parsedPSJ.getResultBitmap();
    }
}
