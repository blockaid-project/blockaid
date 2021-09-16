package sql;

import com.google.common.collect.ImmutableSet;
import org.apache.calcite.sql.*;
import solver.Query;
import solver.Schema;

import java.util.*;

public class PrivacyQuerySelect extends PrivacyQuery {
    private final ParsedPSJ parsedPSJ;
    private final ImmutableSet<String> allNormProjColumns;
    private final ImmutableSet<String> allNormThetaColumns;

    public PrivacyQuerySelect(ParserResult parsedSql, SchemaPlusWithKey schema) {
        this(parsedSql, schema, Collections.emptyList(), Collections.emptyList());
    }

    /**
     * Takes "ownership" of arguments.
     */
    public PrivacyQuerySelect(ParserResult parsedSql, SchemaPlusWithKey schema, List<Object> parameters,
                              List<String> paramNames) {
        super(parsedSql, parameters, paramNames);
        parsedPSJ = new ParsedPSJ(getSelectNode(parsedSql), schema, parameters, paramNames);
        allNormProjColumns = ImmutableSet.copyOf(parsedPSJ.getNormalizedProjectColumns());
        allNormThetaColumns = ImmutableSet.copyOf(parsedPSJ.getNormalizedThetaColumns());
    }

    private SqlSelect getSelectNode(ParserResult result) {
        SqlNode node = result.getSqlNode();
        if (node instanceof SqlOrderBy orderByNode) {
            return (SqlSelect) orderByNode.query;
        } else {
            return (SqlSelect) node;
        }
    }

    @Override
    public Set<String> getAllNormalizedProjectColumns() {
        return allNormProjColumns;
    }

    @Override
    public Set<String> getProjectColumnsByIdx(int colIdx) {
        return Set.of(parsedPSJ.getProjectColumns().get(colIdx));
    }

    @Override
    public Set<String> getNormalizedProjectColumnsByIdx(int colIdx) {
        return Set.of(parsedPSJ.getNormalizedProjectColumns().get(colIdx));
    }

    @Override
    public List<String> getThetaColumns() {
        return new ArrayList<>(parsedPSJ.getThetaColumns());
    }

    @Override
    public Set<String> getAllNormalizedThetaColumns() {
        return allNormThetaColumns;
    }

    @Override
    public List<String> getRelations() {
        return new ArrayList<>(parsedPSJ.getRelations());
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
