package edu.berkeley.cs.netsys.privacy_proxy.sql;

import com.google.common.collect.ImmutableSet;
import org.apache.calcite.sql.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Query;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Schema;
import edu.berkeley.cs.netsys.privacy_proxy.solver.UnionQuery;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;

public class PrivacyQueryUnion extends PrivacyQuery {
    private final List<PrivacyQuery> queries;
    private final ImmutableSet<String> relations;
    private final ImmutableSet<String> allNormProjColumns;
    private final ImmutableSet<String> allNormThetaColumns;

    /**
     * Takes "ownership" of arguments.
     */
    public PrivacyQueryUnion(ParserResult parsedSql, SchemaPlusWithKey schema, List<Object> parameters,
                             List<String> paramNames) {
        super(parsedSql, parameters, paramNames);
        checkArgument(parsedSql.getSqlNode() instanceof SqlBasicCall);
        SqlBasicCall unionNode = (SqlBasicCall) parsedSql.getSqlNode();
        queries = new ArrayList<>();
        int paramOffset = 0;
        for (int i = 0; i < unionNode.operandCount(); ++i) {
            SqlNode operand = unionNode.operand(i);
            int paramCount = (" " + operand.toString() + " ").split("\\?").length - 1;
            List<Object> partParameters = parameters.subList(paramOffset, paramOffset + paramCount);
            List<String> partParamNames = paramNames.subList(paramOffset, paramOffset + paramCount);
            PrivacyQuery query = PrivacyQueryFactory.createPrivacyQuery(new ParserResult(operand), schema,
                    partParameters, partParamNames);
            queries.add(query);

            paramOffset += paramCount;
        }
        relations = queries.stream()
                .flatMap(q -> q.getRelations().stream())
                .collect(ImmutableSet.toImmutableSet());
        allNormProjColumns = queries.stream()
                .flatMap(q -> q.getAllNormalizedProjectColumns().stream())
                .collect(ImmutableSet.toImmutableSet());
        allNormThetaColumns = queries.stream()
                .flatMap(q -> q.getAllNormalizedThetaColumns().stream())
                .collect(ImmutableSet.toImmutableSet());
    }

    @Override
    public Set<String> getAllNormalizedProjectColumns() {
        return allNormProjColumns;
    }

    @Override
    public Set<String> getProjectColumnsByIdx(int colIdx) {
        return queries.stream().flatMap(q -> q.getProjectColumnsByIdx(colIdx).stream()).collect(Collectors.toSet());
    }

    @Override
    public Set<String> getNormalizedProjectColumnsByIdx(int colIdx) {
        return queries.stream().flatMap(q -> q.getNormalizedProjectColumnsByIdx(colIdx).stream())
                .collect(Collectors.toSet());
    }

    @Override
    public List<String> getThetaColumns() {
        List<String> result = new ArrayList<>();
        for (PrivacyQuery query : queries) {
            result.addAll(query.getThetaColumns());
        }
        return result;
    }

    @Override
    public Set<String> getAllNormalizedThetaColumns() {
        return allNormThetaColumns;
    }

    @Override
    public ImmutableSet<String> getRelations() {
        return relations;
    }

    @Override
    public Query getSolverQuery(Schema schema) {
        return new UnionQuery(queries.stream().map(q -> q.getSolverQuery(schema)).toArray(Query[]::new));
    }

    @Override
    public Query getSolverQuery(Schema schema, String paramPrefix, int offset) {
        Query[] q = new Query[queries.size()];
        for (int i = 0; i < queries.size(); ++i) {
            q[i] = queries.get(i).getSolverQuery(schema, paramPrefix, offset);
            offset += queries.get(i).parameters.size();
        }
        return new UnionQuery(q);
    }

    @Override
    public List<Boolean> getResultBitmap() {
        if (queries.isEmpty()) {
            return Collections.emptyList();
        }
        List<Boolean> bitmap = queries.get(0).getResultBitmap();
        for (PrivacyQuery query : queries) {
            List<Boolean> bitmap1 = query.getResultBitmap();
            if (bitmap1.size() < bitmap.size()) {
                List<Boolean> temp = bitmap;
                bitmap = bitmap1;
                bitmap1 = temp;
            }
            for (int i = 0; i < bitmap.size(); ++i) {
                bitmap.set(i, bitmap.get(i) && bitmap1.get(i));
            }
        }
        return bitmap;
    }
}
