package edu.berkeley.cs.netsys.privacy_proxy.sql.preprocess;

import edu.berkeley.cs.netsys.privacy_proxy.sql.ParserResult;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuerySelect;
import edu.berkeley.cs.netsys.privacy_proxy.sql.SchemaPlusWithKey;
import edu.berkeley.cs.netsys.privacy_proxy.util.LogLevel;
import edu.berkeley.cs.netsys.privacy_proxy.util.Logger;
import edu.berkeley.cs.netsys.privacy_proxy.util.SqlNodes;
import org.apache.calcite.sql.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Splits a query with an `IN` operator into multiple queries whose union is equivalent to the original query.
 */
public class SplitIn {
    public static List<PrivacyQuery> perform(PrivacyQuerySelect pq, SchemaPlusWithKey schema) {
        List<Integer> inOperandIndices;
        SqlNode newNode;
        try {
            CollapseInOperator c = new CollapseInOperator();
            newNode = pq.parserResult.getSqlNode().accept(c);
            inOperandIndices = c.inOperandIndices;
        } catch (UnsupportedOperationException e) {
            return List.of(pq);
        }

        if (inOperandIndices == null) { // There is no non-trivial `IN` operator.
            return List.of(pq);
        }
        ShiftDynParams.Result res = ShiftDynParams.perform(newNode, pq.parameters, pq.paramNames);
        ParserResult newParserResult = new ParserResult(res.node());
        int newInOperandIndex = Objects.requireNonNull(res.oldToNew().get(inOperandIndices.get(0)));

        ArrayList<PrivacyQuery> queries = new ArrayList<>();
        for (int oldIndex : inOperandIndices) {
            List<Object> newParams = new ArrayList<>(res.params());
            newParams.set(newInOperandIndex, pq.parameters.get(oldIndex));
            List<String> newParamNames = new ArrayList<>(res.paramNames());
            newParamNames.set(newInOperandIndex, pq.paramNames.get(oldIndex));
            queries.add(new PrivacyQuerySelect(newParserResult, schema, newParams, newParamNames));
            Logger.printMessage(() -> "Split in: " + newParserResult.getParsedSql() + "\t" + newParams, LogLevel.VERBOSE);
        }
        return queries;
    }

    private static class CollapseInOperator extends SqlTransformer {
        private ArrayList<Integer> inOperandIndices;

        @Override
        public SqlNode visit(SqlCall sqlCall) {
            return switch (sqlCall.getKind()) {
                case NOT -> throw new UnsupportedOperationException("NOT is not supported");
                case IN -> {
                    SqlNodeList children = sqlCall.operand(1);
                    if (children.size() <= 1) {
                        yield sqlCall;
                    }

                    if (inOperandIndices != null) {
                        throw new UnsupportedOperationException("more than one IN operator");
                    }
                    inOperandIndices = new ArrayList<>();
                    for (SqlNode child : children) {
                        if (!(child instanceof SqlDynamicParam p)) {
                            throw new UnsupportedOperationException("IN operator contains non-dynamic parameter");
                        }
                        inOperandIndices.add(p.getIndex());
                    }
                    SqlNodeList newChildren = new SqlNodeList(List.of(children.get(0)), children.getParserPosition());
                    SqlCall newCall = SqlNodes.shallowCopy(sqlCall);
                    newCall.setOperand(1, newChildren);
                    yield newCall;
                }
                default -> super.visit(sqlCall);
            };
        }
    }
}
