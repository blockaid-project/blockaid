package sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.util.SqlVisitor;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;

/**
 * Shifts dynamic parameter index and names after some params are REMOVED.
 */
class ShiftDynParams {
    record Result(SqlNode node, List<Object> params, List<String> paramNames) {}

    static Result perform(SqlNode node, List<Object> params, List<String> paramNames) {
        checkArgument(params.size() == paramNames.size());
        List<Integer> sortedIndices = node.accept(GatherDynParamIndices.INSTANCE).sorted().collect(Collectors.toList());
        if (!params.isEmpty()) {
            checkArgument(sortedIndices.get(0) >= 0);
            checkArgument(sortedIndices.get(sortedIndices.size() - 1) < params.size());
        }

        if (sortedIndices.size() == params.size()) { // All parameters are still there.
            return new Result(node, params, paramNames);
        }

        Map<Integer, Integer> oldToNew = new HashMap<>();
        for (Integer oldIndex : sortedIndices) {
            checkArgument(!oldToNew.containsKey(oldIndex), "duplicate dyn param index: " + oldIndex);
            int newIndex = oldToNew.size();
            oldToNew.put(oldIndex, newIndex);
        }

        ArrayList<Object> newParams = new ArrayList<>();
        ArrayList<String> newParamNames = new ArrayList<>();
        for (Integer oldIndex : sortedIndices) {
            newParams.add(params.get(oldIndex));
            newParamNames.add(paramNames.get(oldIndex));
        }

        return new Result(node.accept(new DynParamRewriter(oldToNew)), newParams, newParamNames);
    }

    private static class GatherDynParamIndices implements SqlVisitor<Stream<Integer>> {
        public static final GatherDynParamIndices INSTANCE = new GatherDynParamIndices();

        @Override
        public Stream<Integer> visit(SqlLiteral sqlLiteral) {
            return Stream.empty();
        }

        @Override
        public Stream<Integer> visit(SqlCall sqlCall) {
            return visit(sqlCall.getOperandList());
        }

        public Stream<Integer> visit(List<SqlNode> list) {
            return list.stream().filter(Objects::nonNull).flatMap(node -> node.accept(this));
        }

        @Override
        public Stream<Integer> visit(SqlNodeList sqlNodeList) {
            return visit(sqlNodeList.getList());
        }

        @Override
        public Stream<Integer> visit(SqlIdentifier sqlIdentifier) {
            return Stream.empty();
        }

        @Override
        public Stream<Integer> visit(SqlDataTypeSpec sqlDataTypeSpec) {
            return Stream.empty();
        }

        @Override
        public Stream<Integer> visit(SqlDynamicParam sqlDynamicParam) {
            return Stream.of(sqlDynamicParam.getIndex());
        }

        @Override
        public Stream<Integer> visit(SqlIntervalQualifier sqlIntervalQualifier) {
            throw new RuntimeException("not supported: SqlIntervalQualifier");
        }
    }

    private static class DynParamRewriter extends SqlTransformer {
        private final Map<Integer, Integer> m; // Old index -> new index.

        private DynParamRewriter(Map<Integer, Integer> m) {
            this.m = m;
        }

        @Override
        public SqlNode visit(SqlDynamicParam sqlDynamicParam) {
            int oldIndex = sqlDynamicParam.getIndex();
            int newIndex = m.get(oldIndex);
            if (newIndex == oldIndex) {
                return sqlDynamicParam;
            }
            return new SqlDynamicParam(newIndex, sqlDynamicParam.getParserPosition());
        }
    }
}
