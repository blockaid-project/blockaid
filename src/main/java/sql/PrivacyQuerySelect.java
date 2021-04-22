package sql;

import org.apache.calcite.sql.*;
import solver.Query;
import solver.Schema;

import java.util.*;

public class PrivacyQuerySelect extends PrivacyQuery {
    private ParsedPSJ parsedPSJ;

    public PrivacyQuerySelect(ParserResult parsedSql, SchemaPlusWithKey schema) {
        this(parsedSql, schema, new Object[0], Collections.emptyList());
    }

    public PrivacyQuerySelect(ParserResult parsedSql, SchemaPlusWithKey schema, Object[] parameters, List<String> paramNames) {
        super(parsedSql, parameters, paramNames);
        // `this.parameters` and `this.paramNames` are copies made in `super`.
        parsedPSJ = new ParsedPSJ(getSelectNode(parsedSql), schema, Arrays.asList(this.parameters), this.paramNames);
//        System.out.println("PrivacyQuerySelect: " + parsedSql.parsedSql + ", " + parsedPSJ);
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
    public List<Boolean> getResultBitmap() {
        return parsedPSJ.getResultBitmap();
    }
}
