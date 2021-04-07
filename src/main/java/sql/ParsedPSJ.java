package sql;

import com.microsoft.z3.*;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.*;
import org.apache.calcite.sql.type.SqlTypeName;
import planner.PrivacyColumn;
import planner.PrivacyTable;
import solver.PSJ;
import solver.Query;
import solver.Schema;
import solver.Tuple;

import java.util.*;
import java.util.stream.Collectors;

public class ParsedPSJ {
    private List<String> relations;
    private List<String> projectColumns;
    private List<String> thetaColumns;
    private List<Object> parameters;
    private List<String> paramNames;
    private SqlBasicCall theta;

    public ParsedPSJ(SqlNode parsedSql, SchemaPlus schema, List<Object> parameters, List<String> paramNames) {
        projectColumns = new ArrayList<>();
        thetaColumns = new ArrayList<>();
        this.parameters = parameters;
        this.paramNames = paramNames;

        SqlSelect sqlSelect = (SqlSelect) parsedSql;
        SqlNode fromClause = sqlSelect.getFrom();
        if (fromClause.getKind() != SqlKind.JOIN) {
            List<String> names = ((SqlIdentifier) sqlSelect.getFrom()).names;
            String relation = names.get(names.size() - 1);
            relations = Collections.singletonList(relation);
        } else {
            relations = extractRelationNames((SqlJoin) fromClause);
        }
        relations = relations.stream().map(String::toUpperCase).collect(Collectors.toList());
        for (SqlNode sn : sqlSelect.getSelectList()) {
            SqlIdentifier identifier = (SqlIdentifier) sn;
            if (identifier.names.get(identifier.names.size() - 1).equals("")) {
                if (identifier.names.size() == 1) {
                    for (String relation : relations) {
                        for (PrivacyColumn column : ((PrivacyTable) schema.getTable(relation)).getColumns()) {
                            projectColumns.add(relation + "." + column.name.toUpperCase());
                        }
                    }
                } else {
                    String relation = identifier.names.get(identifier.names.size() - 2);
                    for (PrivacyColumn column : ((PrivacyTable) schema.getTable(relation)).getColumns()) {
                        projectColumns.add(relation + "." + column.name.toUpperCase());
                    }
                }
            } else {
                projectColumns.add(quantifyName(identifier));
            }
        }

        // not WHERE TRUE, WHERE FALSE
        if (sqlSelect.getWhere() != null && sqlSelect.getWhere().getKind() != SqlKind.LITERAL) {
            theta = (SqlBasicCall) sqlSelect.getWhere();
            if (theta != null) {
                addThetaColumns(theta);
            }
        }
    }

    private List<String> extractRelationNames(SqlJoin join) {
        if (join.getJoinType() != JoinType.COMMA || join.getCondition() != null) {
            throw new RuntimeException("unhandled join type");
        }
        SqlNode left = join.getLeft();
        SqlNode right = join.getRight();
        List<String> relations = new ArrayList<>();
        if (left.getKind() == SqlKind.JOIN) {
            relations.addAll(extractRelationNames((SqlJoin) left));
        } else {
            SqlIdentifier identifier = (SqlIdentifier) left;
            relations.add(identifier.names.get(identifier.names.size() - 1));
        }
        if (right.getKind() == SqlKind.JOIN) {
            relations.addAll(extractRelationNames((SqlJoin) right));
        } else {
            SqlIdentifier identifier = (SqlIdentifier) right;
            relations.add(identifier.names.get(identifier.names.size() - 1));
        }
        return relations;
    }

    private void addThetaColumns(SqlBasicCall predicate) {
        SqlNode left = predicate.operand(0);
        SqlNode right = predicate.operand(1);
        if (left instanceof SqlBasicCall) {
            addThetaColumns((SqlBasicCall) left);
        } else if (left instanceof SqlIdentifier) {
            String name = quantifyName((SqlIdentifier) left);
            if (!name.startsWith("@")) {
                thetaColumns.add(name);
            }
        }
        if (right instanceof SqlBasicCall) {
            addThetaColumns((SqlBasicCall) right);
        } else if (right instanceof SqlIdentifier) {
            String name = quantifyName((SqlIdentifier) right);
            if (!name.startsWith("@")) {
                thetaColumns.add(name);
            }
        }
    }

    private Expr getPredicate(Context context, SqlNode theta, Map<String, Expr> symbolMap, List<Object> params, List<String> paramNames) {
        if (theta instanceof SqlIdentifier) {
            String name = quantifyName((SqlIdentifier) theta);
            if (symbolMap.containsKey(name)) {
                return symbolMap.get(name);
            } else {
                return context.mkConst(context.mkSymbol(name), context.getIntSort());
            }
        } else if (theta instanceof SqlLiteral) {
            SqlLiteral literal = (SqlLiteral) theta;
            if (literal.getTypeName() == SqlTypeName.BOOLEAN) {
                return context.mkBool(literal.booleanValue());
            } else if (literal.getTypeName() == SqlTypeName.INTEGER || literal.getTypeName() == SqlTypeName.DECIMAL) {
                return context.mkInt(literal.intValue(true));
            } else if (literal.getTypeName() == SqlTypeName.CHAR) {
                return context.mkString(literal.toString());
            }
            throw new UnsupportedOperationException("unhandled literal type: " + literal.getTypeName());
        } else if (theta instanceof SqlBasicCall) {
            Expr left = getPredicate(context, ((SqlBasicCall) theta).operand(0), symbolMap, params, paramNames);
            Expr right = getPredicate(context, ((SqlBasicCall) theta).operand(1), symbolMap, params, paramNames);
            if (theta.getKind() == SqlKind.AND) {
                return context.mkAnd((BoolExpr) left, (BoolExpr) right);
            } else if (theta.getKind() == SqlKind.OR) {
                return context.mkOr((BoolExpr) left, (BoolExpr) right);
            } else if (theta.getKind() == SqlKind.EQUALS) {
                return context.mkEq(left, right);
            } else if (theta.getKind() == SqlKind.NOT_EQUALS) {
                return context.mkNot(context.mkEq(left, right));
            } else if (theta.getKind() == SqlKind.LESS_THAN) {
                return context.mkLt((ArithExpr) left, (ArithExpr) right);
            } else if (theta.getKind() == SqlKind.LESS_THAN_OR_EQUAL) {
                return context.mkLe((ArithExpr) left, (ArithExpr) right);
            } else if (theta.getKind() == SqlKind.GREATER_THAN) {
                return context.mkGt((ArithExpr) left, (ArithExpr) right);
            } else if (theta.getKind() == SqlKind.GREATER_THAN_OR_EQUAL) {
                return context.mkGe((ArithExpr) left, (ArithExpr) right);
            }
        } else if (theta instanceof SqlDynamicParam) {
            Object param = params.get(params.size() - 1);
            params.remove(params.size() - 1);
            String name = "@" + paramNames.get(paramNames.size() - 1);
            paramNames.remove(paramNames.size() - 1);
            if (name.equals("@?")) {
                return Tuple.getExprFromObject(context, param);
            } else {
                if (symbolMap.containsKey(name)) {
                    return symbolMap.get(name);
                } else {
                    return context.mkConst(context.mkSymbol(name), context.getIntSort());
                }
            }
        }
        throw new UnsupportedOperationException("where clause uses unsupported operations: " + theta);
    }

    private String quantifyName(SqlIdentifier identifier) {
        List<String> names = identifier.names;
        if (names.size() == 1) {
            if (names.get(0).startsWith("_")) {
                return "@" + names.get(0);
            }
            if (relations.size() != 1) {
                throw new UnsupportedOperationException("joins must only use fully-specified column names");
            }
            return (relations.get(0) + "." + identifier.names.get(0)).toUpperCase();
        } else {
            return (names.get(0) + "." + names.get(1)).toUpperCase();
        }
    }

    public List<String> getProjectColumns() {
        return projectColumns;
    }

    public List<String> getThetaColumns() {
        return thetaColumns;
    }

    public List<String> getRelations() {
        return relations;
    }

    public BoolExpr getPredicate(Context context, Map<String, Expr> symbolMap) {
        if (theta != null) {
            List<Object> params = new ArrayList<>(parameters);
            Collections.reverse(params);
            List<String> names = new ArrayList<>(paramNames);
            Collections.reverse(names);
            return (BoolExpr) getPredicate(context, theta, symbolMap, params, names);
        } else {
            return context.mkTrue();
        }
    }

    public BoolExpr getPredicate(Context context) {
        return getPredicate(context, Collections.emptyMap());
    }

    public Query getSolverQuery(Schema schema) {
        return new SolverQuery(schema);
    }

    private class SolverQuery extends PSJ {
        int[] projectRelationIndex;
        int[] projectColumnIndex;
        int[] thetaRelationIndex;
        int[] thetaColumnIndex;

        public SolverQuery(Schema schema) {
            super(schema, relations);

            projectRelationIndex = new int[projectColumns.size()];
            projectColumnIndex = new int[projectColumns.size()];
            thetaRelationIndex = new int[thetaColumns.size()];
            thetaColumnIndex = new int[thetaColumns.size()];

            mapIndices(schema, projectColumns, projectRelationIndex, projectColumnIndex);
            mapIndices(schema, thetaColumns, thetaRelationIndex, thetaColumnIndex);
        }

        private void mapIndices(Schema schema, List<String> columns, int[] relationIndex, int[] columnIndex) {
            Iterator<String> iter = columns.iterator();
            for (int i = 0; i < columns.size(); ++i) {
                String[] parts = iter.next().split("\\.");
                relationIndex[i] = relations.indexOf(parts[0]);
                if (relationIndex[i] == -1) {
                    throw new RuntimeException("relation not found: " + parts[0] + " in relations " + relations);
                }
                List<String> columnNames = schema.getColumnNames(parts[0]);
                columnIndex[i] = columnNames.indexOf(parts[1]);
                if (relationIndex[i] == -1 || columnIndex[i] == -1) {
                    throw new RuntimeException("column not found: " + parts[0] + "." + parts[1]
                            + " in columns: " + columnNames);
                }
            }
        }

        @Override
        protected BoolExpr predicateGenerator(Context context, Tuple... tuples) {
            Map<String, Expr> map = new HashMap<>();
            for (int i = 0; i < thetaColumnIndex.length; ++i) {
                map.put(thetaColumns.get(i), tuples[thetaRelationIndex[i]].get(thetaColumnIndex[i]));
            }
            return getPredicate(context, map);
        }

        @Override
        protected Tuple headSelector(Tuple... tuples) {
            Expr[] parts = new Expr[projectRelationIndex.length];
            for (int i = 0; i < parts.length; ++i) {
                parts[i] = tuples[projectRelationIndex[i]].get(projectColumnIndex[i]);
            }
            return new Tuple(parts);
        }

        @Override
        protected Sort[] headTypeSelector(Sort[]... types) {
            Sort[] parts = new Sort[projectRelationIndex.length];
            for (int i = 0; i < parts.length; ++i) {
                parts[i] = types[projectRelationIndex[i]][projectColumnIndex[i]];
            }
            return parts;
        }
    }
}
