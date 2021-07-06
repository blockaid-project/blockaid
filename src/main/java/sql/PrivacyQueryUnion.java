package sql;

import org.apache.calcite.sql.*;
import solver.Query;
import solver.Schema;
import solver.UnionQuery;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;

public class PrivacyQueryUnion extends PrivacyQuery {
    private final List<PrivacyQuery> queries;

    /**
     * Takes "ownership" of arguments.
     */
    public PrivacyQueryUnion(ParserResult parsedSql, SchemaPlusWithKey schema, List<Object> parameters,
                             List<String> paramNames, Map<Integer, String> reverseConstMap) {
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
            PrivacyQuery query = PrivacyQueryFactory.createPrivacyQuery(new UnionPartParserResult(operand), schema,
                    partParameters.toArray(new Object[0]), partParamNames, reverseConstMap);
            queries.add(query);

            paramOffset += paramCount;
        }
    }

    @Override
    public List<String> getProjectColumns() {
        List<String> result = new ArrayList<>();
        for (PrivacyQuery query : queries) {
            result.addAll(query.getProjectColumns());
        }
        return result;
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
    public List<String> getRelations() {
        List<String> result = new ArrayList<>();
        for (PrivacyQuery query : queries) {
            result.addAll(query.getRelations());
        }
        return result;
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

    private static class UnionPartParserResult extends ParserResult {
        private UnionPartParserResult(SqlNode node) {
            super(node.toString(), node.getKind(), node, false, false);
        }
    }
}
