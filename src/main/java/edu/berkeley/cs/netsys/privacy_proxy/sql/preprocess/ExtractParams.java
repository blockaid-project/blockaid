package edu.berkeley.cs.netsys.privacy_proxy.sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.parser.SqlParserPos;
import org.apache.calcite.sql.type.SqlTypeName;
import edu.berkeley.cs.netsys.privacy_proxy.sql.ParserResult;
import edu.berkeley.cs.netsys.privacy_proxy.util.SqlNodes;

import java.sql.Timestamp;
import java.time.LocalDateTime;
import java.time.format.DateTimeParseException;
import java.time.temporal.ChronoUnit;
import java.util.List;

public class ExtractParams extends SqlTransformer {
    // Any date-time parameter within this threshold (in seconds) of now is considered as now.
    private static final long NOW_DATETIME_THRESHOLD_S = 60;

    /**
     * Extracts literals in SQL query into parameters.
     *
     * Also finds strings that looks like a datetime close to the current time and transforms them into `_NOW`.
     *
     * @param pr the SQL query.
     * @param params list of existing parameters; to be mutated.
     * @param paramNames list of existing parameter names; to be mutated.
     * @return new SQL query.
     */
    public static ParserResult perform(ParserResult pr, List<Object> params, List<String> paramNames) {
        SqlNode newNode = pr.getSqlNode().accept(new ExtractParams(params, paramNames));
        return new ParserResult(newNode);
    }

    private final List<Object> params;
    private final List<String> paramNames;
    private int i = 0;

    private ExtractParams(List<Object> params, List<String> paramNames) {
        this.params = params;
        this.paramNames = paramNames;
    }

    private SqlNode visitLiteral(Object v, SqlParserPos pos) {
        params.add(i, v);
        paramNames.add(i, "?");
        return new SqlDynamicParam(i, pos).accept(this);
    }

    @Override
    public SqlNode visit(SqlLiteral sqlLiteral) {
        Object v = switch (sqlLiteral.getTypeName()) {
            case BOOLEAN -> sqlLiteral.booleanValue();
            case INTEGER -> sqlLiteral.intValue(true);
            case DECIMAL -> sqlLiteral.bigDecimalValue();
            case CHAR -> sqlLiteral.getValueAs(String.class);
//            case SYMBOL -> sqlLiteral;
            default -> throw new RuntimeException("unhandled literal type: " + sqlLiteral.getTypeName());
        };
        return visitLiteral(v, sqlLiteral.getParserPosition());
    }

    private boolean isCloseToDateTimeNow(Object v) {
        if (!(v instanceof Timestamp ts)) {
            return false;
        }

        LocalDateTime now = LocalDateTime.now();
        LocalDateTime ldt = ts.toLocalDateTime();
        return Math.abs(ldt.until(now, ChronoUnit.SECONDS)) <= NOW_DATETIME_THRESHOLD_S;
    }

    @Override
    public SqlNode visit(SqlDynamicParam sqlDynamicParam) {
        if (isCloseToDateTimeNow(params.get(i))) {
            params.remove(i);
            paramNames.remove(i);
            return new SqlIdentifier("_NOW", sqlDynamicParam.getParserPosition());
        }

        i += 1;
        if (sqlDynamicParam.getIndex() == i - 1) {
            return sqlDynamicParam;
        }
        return new SqlDynamicParam(i - 1, sqlDynamicParam.getParserPosition());
    }

    @Override
    public SqlNode visit(SqlCall sqlCall) {
        return switch (sqlCall.getKind()) {
            case SELECT -> {
                SqlSelect newSelect = (SqlSelect) SqlNodes.shallowCopy(sqlCall);
                newSelect.setFrom(newSelect.getFrom().accept(this));
                SqlNode where = newSelect.getWhere();
                if (where != null) { newSelect.setWhere(where.accept(this)); }
                if (newSelect.getGroup() != null) { throw new RuntimeException("not supported (group): " + sqlCall); }
                if (!newSelect.getWindowList().isEmpty()) {
                    throw new RuntimeException("not supported (window): " + sqlCall);
                }
                if (newSelect.getHaving() != null) { throw new RuntimeException("not supported (having): " + sqlCall); }
                if (newSelect.getOffset() != null) { throw new RuntimeException("not supported (offset): " + sqlCall); }
                SqlNode fetch = newSelect.getFetch();
                if (fetch != null) { newSelect.setFetch(fetch.accept(this)); }
                yield newSelect;
            }
            case JOIN -> {
                SqlJoin join = (SqlJoin) sqlCall;
                SqlNode newLeft = join.getLeft().accept(this);
                SqlNode newRight = join.getRight().accept(this);
                SqlNode condition = join.getCondition();
                SqlNode newCondition = null;
                if (condition != null) {
                    newCondition = condition.accept(this);
                }
                yield new SqlJoin(join.getParserPosition(), newLeft, join.isNaturalNode(), join.getJoinTypeNode(),
                        newRight, join.getConditionTypeNode(), newCondition);
            }
            case CAST -> {
                List<SqlNode> operands = sqlCall.getOperandList();
                if (!(operands.get(0) instanceof SqlLiteral literal)) {
                    throw new RuntimeException("not supported: " + sqlCall);
                }
                if (literal.getTypeName() != SqlTypeName.CHAR) {
                    throw new RuntimeException("cast literal not supported: " + literal);
                }
                String s = literal.getValueAs(String.class);

                SqlDataTypeSpec spec = (SqlDataTypeSpec) operands.get(1);
                if (!(spec.getTypeNameSpec() instanceof SqlBasicTypeNameSpec basicSpec)) {
                    throw new RuntimeException("cast type spec not supported: " + spec);
                }

                if (basicSpec.getTypeName().names.size() != 1) {
                    throw new RuntimeException("spec name not supported: " + basicSpec.getTypeName());
                }
                String typeName = basicSpec.getTypeName().names.get(0);
                if (typeName.equals("TIMESTAMP")) {
                    LocalDateTime ldt;
                    // We expect the datetime to look like '2021-08-13 03:04:40.605143'.
                    // https://stackoverflow.com/questions/30135025/java-date-parsing-with-microsecond-or-nanosecond-accuracy
                    try {
                        ldt = LocalDateTime.parse(s.replace(" ", "T"));
                    } catch (DateTimeParseException e) {
                        throw new RuntimeException(e);
                    }
                    yield visitLiteral(Timestamp.valueOf(ldt), sqlCall.getParserPosition());
                }
                throw new RuntimeException("type not supported: " + typeName);
            }
            default -> super.visit(sqlCall);
        };
    }
}
