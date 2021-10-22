package edu.berkeley.cs.netsys.privacy_proxy.sql;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import org.apache.calcite.sql.*;
import org.apache.calcite.sql.type.SqlTypeName;
import edu.berkeley.cs.netsys.privacy_proxy.solver.*;
import edu.berkeley.cs.netsys.privacy_proxy.util.UnionFind;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class ParsedPSJ {
    private final List<String> relations;
    private boolean hasRelAlias = false;
    private final Map<String, Integer> relAliasToIdx;
    private final List<String> projectColumns;
    private final List<String> thetaColumns;
    private final List<Object> parameters;
    private final List<String> paramNames;
    private final LinkedHashMap<SqlBasicCall, PredicateInfo> theta; // identical predicates are not equal so this works
    private final boolean trivialWhereClause;
    private List<Boolean> resultBitmap;

    private static class PredicateInfo {
        private final List<String> columns = new ArrayList<>();
        private int parameterOffset = -1;
        private int parameterCount = 0;
    }

    public ParsedPSJ(SqlNode parsedSql, SchemaPlusWithKey schema, List<Object> parameters, List<String> paramNames) {
        projectColumns = new ArrayList<>();
        this.relAliasToIdx = new HashMap<>(); // Maps relation aliases (and alias-less relation names) to index.
        this.parameters = parameters;
        this.paramNames = paramNames;
        this.theta = new LinkedHashMap<>();
        this.resultBitmap = new ArrayList<>();

        SqlSelect sqlSelect = (SqlSelect) parsedSql;
        SqlNode fromClause = sqlSelect.getFrom();
        // innermost subquery while no joins in from
        while (fromClause.getKind() == SqlKind.AS && (((SqlBasicCall) fromClause).operand(0) instanceof SqlSelect || ((SqlBasicCall) fromClause).operand(0) instanceof SqlOrderBy)) {
            if (((SqlBasicCall) fromClause).operand(0) instanceof SqlOrderBy) {
                sqlSelect = (SqlSelect) ((SqlOrderBy) ((SqlBasicCall) fromClause).operand(0)).query;
            } else {
                sqlSelect = ((SqlBasicCall) fromClause).operand(0);
            }
            fromClause = sqlSelect.getFrom();
            this.resultBitmap = null;
        }
        relations = new ArrayList<>();
        if (fromClause.getKind() != SqlKind.JOIN) {
            addRelationName(fromClause);
        } else {
            extractRelationNames((SqlJoin) fromClause);
        }
        for (SqlNode sn : sqlSelect.getSelectList()) {
            // ignore unary function calls and use whatever they're called with instead
            boolean addPrimaryKey = false;
            while (sn instanceof SqlBasicCall call) {
                if (call.getOperator() instanceof SqlAsOperator) {
                    SqlNode op0 = call.operand(0);
                    if (!(op0.getKind() == SqlKind.LITERAL || op0.getKind() == SqlKind.IDENTIFIER)) {
                        throw new RuntimeException("only literal & identifier aliases are handled");
                    }
                    sn = op0;
                    continue;
                }
                if (call.operandCount() != 1) { // only supporting unary functions
                    throw new RuntimeException("only supporting unary functions");
                }
                sn = call.getOperands()[0];
                this.resultBitmap = null;
                addPrimaryKey = true;
            }

            if (sn instanceof SqlLiteral) {
                resultBitmap.add(false);
                continue;
            }

            SqlIdentifier identifier = (SqlIdentifier) sn;

            if (addPrimaryKey) {
                if (hasRelAlias) {
                    throw new RuntimeException("not supported: relation alias");
                }
                if (identifier.names.size() == 1) {
                    for (String relation : relations) {
                        for (String column : schema.getPrimaryKeyColumns(relation).get()) {
                            projectColumns.add((relation + "." + column).toUpperCase());
                        }
                    }
                } else {
                    String relation = identifier.names.get(0).toUpperCase();
                    for (String column : schema.getPrimaryKeyColumns(relation).get()) {
                        projectColumns.add((relation + "." + column).toUpperCase());
                    }
                }
            }

            if (identifier.names.get(identifier.names.size() - 1).equals("")) {
                if (identifier.names.size() == 1) { // SELECT * FROM ...
                    if (hasRelAlias) {
                        throw new RuntimeException("not supported: relation alias");
                    }
                    for (String relation : relations) {
                        schema.getColumnNames(relation).forEach(col -> {
                            addProjectColumn((relation + "." + col).toUpperCase());
                        });
                    }
                } else { // SELECT table.* FROM ...
                    String quantifier = identifier.names.get(identifier.names.size() - 2).toUpperCase();
                    String relation = relations.get(relAliasToIdx.get(quantifier));
                    schema.getColumnNames(relation).forEach(col -> {
                        addProjectColumn((quantifier + "." + col).toUpperCase());
                    });
                }
            } else {
                addProjectColumn(quantifyName(identifier));
            }
        }

        // not WHERE TRUE, WHERE FALSE - converted to WHERE ?
        if (sqlSelect.getWhere() != null && sqlSelect.getWhere().getKind() != SqlKind.DYNAMIC_PARAM) {
            SqlBasicCall mainTheta = (SqlBasicCall) sqlSelect.getWhere();
            if (mainTheta != null) {
                addTheta(mainTheta);
            }
            trivialWhereClause = false;
        } else if (sqlSelect.getWhere() != null) {
            Object value = parameters.get(parameters.size() - 1);
            checkNotNull(value);
            checkArgument(value instanceof Boolean);
            trivialWhereClause = true;
        } else {
            trivialWhereClause = false;
        }

        this.thetaColumns = new ArrayList<>();
        int parameterOffset = 0;
        for (PredicateInfo info : this.theta.values()) {
            this.thetaColumns.addAll(info.columns);
            info.parameterOffset = parameterOffset;
            parameterOffset += info.parameterCount;
        }
    }

    private ParsedPSJ(List<String> relations, boolean hasRelAlias, Map<String, Integer> relAliasToIdx,
                     List<String> projectColumns, List<Object> parameters,
                     List<String> paramNames, List<SqlBasicCall> theta, boolean trivialWhereClause) {
        this.relations = relations;
        this.hasRelAlias = hasRelAlias;
        this.relAliasToIdx = relAliasToIdx;
        this.projectColumns = new ArrayList<>();
        this.thetaColumns = new ArrayList<>();
        this.parameters = parameters;
        this.paramNames = paramNames;
        this.theta = new LinkedHashMap<>();
        this.trivialWhereClause = trivialWhereClause;
        this.resultBitmap = null;

        for (String col : projectColumns) {
            addProjectColumn(col);
        }
        for (SqlBasicCall t : theta) {
            addTheta(t);
        }
        int parameterOffset = 0;
        for (PredicateInfo info : this.theta.values()) {
            this.thetaColumns.addAll(info.columns);
            info.parameterOffset = parameterOffset;
            parameterOffset += info.parameterCount;
        }
    }

    // Change column quantifier to relation name if it's an alias.
    private String normalizeColumn(String column) {
        String[] parts = column.split("\\.");
        String quantifier = parts[0]; // A quantifier can either be a relation name or an alias.

        int currIdx = relAliasToIdx.get(quantifier);
        String relationName = relations.get(currIdx);
        return relationName + "." + parts[1];
    }

    private String getRelationNameForAlias(String alias) {
        return relations.get(relAliasToIdx.get(alias));
    }

    private void addProjectColumn(String column) {
        projectColumns.add(column);
        if (resultBitmap != null) {
            resultBitmap.add(true);
        }
    }

    private void extractRelationNames(SqlJoin join) {
        if (join.getJoinType() != JoinType.COMMA && join.getJoinType() != JoinType.INNER) {
            throw new RuntimeException("unhandled join type: " + join.getJoinType() + ", " + join.getCondition());
        }
        SqlNode left = join.getLeft();
        SqlNode right = join.getRight();
        if (left.getKind() == SqlKind.JOIN) {
            extractRelationNames((SqlJoin) left);
        } else {
            addRelationName(left);
        }
        if (right.getKind() == SqlKind.JOIN) {
            extractRelationNames((SqlJoin) right);
        } else {
            addRelationName(right);
        }

        if (join.getCondition() != null && join.getCondition().getKind() != SqlKind.LITERAL) {
            addTheta((SqlBasicCall) join.getCondition());
        }
    }

    private void addRelationName(SqlNode node) {
        String alias = null;
        if (node.getKind() == SqlKind.AS) {
            SqlBasicCall call = (SqlBasicCall) node;
            SqlNode rhs = call.operand(1);
            ImmutableList<String> names = ((SqlIdentifier) rhs).names;
            if (names.size() > 1) {
                throw new RuntimeException("not supported: multipart table alias: " + rhs);
            }
            alias = names.get(0).toUpperCase();
            node = call.operand(0);
        }

        SqlIdentifier identifier = (SqlIdentifier) node;
        String relationName = identifier.names.get(identifier.names.size() - 1).toUpperCase();
        relations.add(relationName);
        if (alias != null && !alias.equals(relationName)) {
            hasRelAlias = true;
            relAliasToIdx.put(alias, relations.size() - 1);
        } else {
            if (relAliasToIdx.containsKey(relationName)) {
                throw new RuntimeException("duplicate relation name: " + relationName);
            }
            relAliasToIdx.put(relationName, relations.size() - 1);
        }
    }

    private void addTheta(SqlBasicCall predicate) {
        addTheta(predicate, null);
    }

    private void addTheta(SqlBasicCall predicate, PredicateInfo info) {
        boolean isAnd = (predicate.getKind() == SqlKind.AND);
        if (info == null && !isAnd) {
            info = new PredicateInfo();
            theta.put(predicate, info);
        }

        SqlNode left = predicate.operand(0);
        SqlNode right = predicate.operand(1);
        if (left instanceof SqlBasicCall) {
            addTheta((SqlBasicCall) left, info);
        } else if (left instanceof SqlIdentifier) {
            String name = quantifyName((SqlIdentifier) left);
            if (!name.startsWith("!")) {
                info.columns.add(name);
            }
        } else if (left instanceof SqlDynamicParam) {
            ++info.parameterCount;
        }
        if (right instanceof SqlBasicCall) {
            addTheta((SqlBasicCall) right, info);
        } else if (right instanceof SqlIdentifier) {
            String name = quantifyName((SqlIdentifier) right);
            if (!name.startsWith("!")) {
                info.columns.add(name);
            }
        } else if (right instanceof SqlDynamicParam) {
            ++info.parameterCount;
        }
    }

    private Expr getPredicate(SqlNode theta, Map<String, Expr> symbolMap, List<Object> params, List<String> paramNames, Schema schema) {
        Z3ContextWrapper context = schema.getContext();
        if (theta instanceof SqlIdentifier identifier) {
            String name = quantifyName(identifier);
            if (symbolMap.containsKey(name)) {
                return symbolMap.get(name);
            } else if (!name.startsWith("!")) {
                String[] parts = name.split("\\.", 2);
                checkArgument(parts.length == 2, "not a two-part name: %s", name);
                String relationName = getRelationNameForAlias(parts[0]);
                List<Column> columns = schema.getColumns(relationName);
                for (Column column : columns) {
                    if (column.name.toUpperCase().equals(parts[1])) {
                        return context.mkConst(name, column.type);
                    }
                }

                throw new RuntimeException("unknown type for column " + name);
            } else {
                return context.mkConst(name, context.getCustomIntSort());
            }
        } else if (theta instanceof SqlLiteral literal) {
            if (literal.getTypeName() == SqlTypeName.BOOLEAN) {
                return context.mkCustomBool(literal.booleanValue());
            } else if (literal.getTypeName() == SqlTypeName.INTEGER || literal.getTypeName() == SqlTypeName.DECIMAL) {
                return context.mkCustomInt(literal.intValue(true));
            } else if (literal.getTypeName() == SqlTypeName.CHAR) {
                return context.mkCustomString(literal.getValueAs(String.class));
            }
            throw new UnsupportedOperationException("unhandled literal type: " + literal.getTypeName());
        } else if (theta instanceof SqlBasicCall call) {
            Expr left = getPredicate(call.operand(0), symbolMap, params, paramNames, schema);

            if (theta.getKind() == SqlKind.IN || theta.getKind() == SqlKind.NOT_IN) {
                final Expr left1 = left;
                SqlNodeList values = call.operand(1);
                BoolExpr[] exprs = values.getList().stream()
                        .map(n -> context.mkEq(left1, getPredicate(n, symbolMap, params, paramNames, schema)))
                        .toArray(BoolExpr[]::new);
                BoolExpr expr = context.mkOr(exprs);
                if (theta.getKind() == SqlKind.NOT_IN) {
                    expr = context.mkNot(expr);
                }
                return expr;
            }

            Expr right = getPredicate(((SqlBasicCall) theta).operand(1), symbolMap, params, paramNames, schema);
            if (left instanceof ArithExpr && right instanceof SeqExpr) {
                try {
                    new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").parse(right.getString()).getTime();
                    throw new RuntimeException(); // TODO: is this ever used
                } catch (ParseException e) {
                    // do nothing
                }
            } else if (right instanceof ArithExpr && left instanceof SeqExpr) {
                try {
                    new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").parse(left.getString()).getTime();
                    throw new RuntimeException(); // TODO: is this ever used
                } catch (ParseException e) {
                    // do nothing
                }
            }
            if (theta.getKind() == SqlKind.AND) {
                return context.mkAnd((BoolExpr) left, (BoolExpr) right);
            } else if (theta.getKind() == SqlKind.OR) {
                return context.mkOr((BoolExpr) left, (BoolExpr) right);
            } else if (theta.getKind() == SqlKind.EQUALS) {
                return context.mkEq(left, right);
            } else if (theta.getKind() == SqlKind.NOT_EQUALS) {
                return context.mkNot(context.mkEq(left, right));
            } else if (theta.getKind() == SqlKind.LESS_THAN) {
                return context.mkCustomIntLt(left, right);
//            } else if (theta.getKind() == SqlKind.LESS_THAN_OR_EQUAL) {
//                return context.mkLe((ArithExpr) left, (ArithExpr) right);
            } else if (theta.getKind() == SqlKind.GREATER_THAN) {
                return context.mkCustomIntLt(right, left);
//            } else if (theta.getKind() == SqlKind.GREATER_THAN_OR_EQUAL) {
//                return context.mkGe((ArithExpr) left, (ArithExpr) right);
            }
        } else if (theta instanceof SqlDynamicParam) {
            Object param = params.get(params.size() - 1);
            params.remove(params.size() - 1);
            String name = "!" + paramNames.get(paramNames.size() - 1);
            paramNames.remove(paramNames.size() - 1);
            if (name.equals("!?")) {
                if (param == null) {
                    throw new UnsupportedOperationException("null parameter is not supported (yet)");
                }
                return context.getExprForValue(param);
            } else {
                if (symbolMap.containsKey(name)) {
                    return symbolMap.get(name);
                } else {
                    return context.mkConst(name, context.getSortForValue(param));
                }
            }
        }
        throw new UnsupportedOperationException("where clause uses unsupported operations: " + theta);
    }

    private String quantifyName(SqlIdentifier identifier) {
        List<String> names = identifier.names;
        if (names.size() == 1) {
            if (names.get(0).startsWith("_")) {
                return "!" + names.get(0);
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

    public List<String> getNormalizedProjectColumns() {
        return projectColumns.stream().map(this::normalizeColumn).collect(Collectors.toList());
    }

    public List<String> getThetaColumns() {
        return thetaColumns;
    }

    public List<String> getNormalizedThetaColumns() {
        return thetaColumns.stream().map(this::normalizeColumn).collect(Collectors.toList());
    }

    public List<String> getRelations() {
        return relations;
    }

    private BoolExpr getPredicate(Map<String, Expr> symbolMap, Schema schema, String prefix, int parameterOffset) {
        Z3ContextWrapper context = schema.getContext();
        if (theta != null && theta.size() > 0) {
            List<Object> params = new ArrayList<>(parameters);
            Collections.reverse(params);
            List<String> names = new ArrayList<>(paramNames);
            if (prefix != null) {
                for (int i = 0; i < names.size(); ++i) {
                    if (names.get(i).equals("?")) {
                        names.set(i, prefix + "!" + (i + parameterOffset));
                    }
                }
            }
            Collections.reverse(names);
            BoolExpr[] exprs = new BoolExpr[theta.size()];
            Iterator<SqlBasicCall> iter = theta.keySet().iterator();
            for (int i = 0; i < theta.size(); ++i) {
                exprs[i] = (BoolExpr) getPredicate(iter.next(), symbolMap, params, names, schema);
            }
            return context.mkAnd(exprs);
        } else {
            if (trivialWhereClause) {
                Boolean value = (Boolean) parameters.get(parameters.size() - 1);
                return context.mkBool(value);
            }
            return context.mkTrue();
        }
    }

    public BoolExpr getPredicate(Schema schema) {
        return getPredicate(Collections.emptyMap(), schema, null, 0);
    }

    public Query getSolverQuery(Schema schema) {
        return getSolverQuery(schema, null, 0);
    }

    public Query getSolverQuery(Schema schema, String prefix, int offset) {
        return new SolverQuery(schema, prefix, offset);
    }

    public List<Boolean> getResultBitmap() {
        return resultBitmap == null ? Collections.emptyList() : resultBitmap;
    }

    /**
     * Checks if this policy has no `WHERE` clause, i.e., returns all rows.
     * @return true if this policy has no `WHERE` clause.
     */
    public boolean hasNoTheta() {
        return theta.isEmpty();
    }

    private class SolverQuery extends PSJ {
        int[] projectRelationIndex;
        int[] projectColumnIndex;
        int[] thetaRelationIndex;
        int[] thetaColumnIndex;
        Schema schema;
        String prefix;
        int parameterOffset;

        private SolverQuery(Schema schema, String prefix, int parameterOffset) {
            super(schema, relations);

            projectRelationIndex = new int[projectColumns.size()];
            projectColumnIndex = new int[projectColumns.size()];
            thetaRelationIndex = new int[thetaColumns.size()];
            thetaColumnIndex = new int[thetaColumns.size()];

            this.schema = schema;
            this.prefix = prefix;
            this.parameterOffset = parameterOffset;

            mapIndices(schema, projectColumns, projectRelationIndex, projectColumnIndex);
            mapIndices(schema, thetaColumns, thetaRelationIndex, thetaColumnIndex);
        }

        private void mapIndices(Schema schema, List<String> columns, int[] relationIndex, int[] columnIndex) {
            Iterator<String> iter = columns.iterator();
            for (int i = 0; i < columns.size(); ++i) {
                String[] parts = iter.next().split("\\.");
                String quantifier = parts[0]; // A quantifier can either be a relation name or an alias.

                int currIdx = relAliasToIdx.get(quantifier);
                relationIndex[i] = currIdx;

                String relationName = relations.get(currIdx);
                List<String> columnNames = schema.getColumnNames(relationName);
                columnIndex[i] = columnNames.indexOf(parts[1]);
                if (relationIndex[i] == -1 || columnIndex[i] == -1) {
                    throw new RuntimeException("column not found: " + relationName + "." + parts[1]
                            + " in columns: " + columnNames);
                }
            }
        }

        public Iterable<Query> getComponents() {
            UnionFind<String> uf = new UnionFind<>(relAliasToIdx.keySet());
            for (PredicateInfo info : theta.values()) {
                List<String> thetaColumns = info.columns;
                if (thetaColumns.size() < 2) {
                    continue;
                }
                for (int i = 0; i < thetaColumns.size() - 1; ++i) {
                    uf.union(thetaColumns.get(i).split("\\.", 2)[0], thetaColumns.get(i + 1).split("\\.", 2)[0]);
                }
            }
            Map<String, Set<String>> components = new HashMap<>();
            for (String relation : relAliasToIdx.keySet()) {
                String root = uf.find(relation);
                components.putIfAbsent(root, new HashSet<>());
                components.get(root).add(relation);
            }
            if (components.size() == 1) {
                return super.getComponents();
            }
            List<Query> queries = new ArrayList<>();
            for (Set<String> component : components.values()) {
                List<String> componentRelations = new ArrayList<>();
                boolean componentHasRelAlias = false;
                Map<String, Integer> componentRelAliasToIdx = new HashMap<>();
                for (String alias : component) {
                    String relation = relations.get(relAliasToIdx.get(alias));
                    componentRelAliasToIdx.put(alias, componentRelations.size());
                    componentRelations.add(relation);
                    componentHasRelAlias = componentHasRelAlias || !relation.equals(alias);
                }

                List<String> componentProjectColumns = projectColumns.stream()
                        .filter(col -> component.contains(col.split("\\.", 2)[0]))
                        .collect(Collectors.toList());
                List<Object> componentParameters = new ArrayList<>();
                List<String> componentParamNames = new ArrayList<>();
                List<SqlBasicCall> componentTheta = new ArrayList<>();
                for (Map.Entry<SqlBasicCall, PredicateInfo> entry : theta.entrySet()) {
                    PredicateInfo info = entry.getValue();
                    if (info.columns.stream().map(c -> c.split("\\.", 2)[0]).anyMatch(component::contains)) {
                        componentTheta.add(entry.getKey());
                        componentParameters.addAll(parameters.subList(info.parameterOffset, info.parameterOffset + info.parameterCount));
                        componentParamNames.addAll(paramNames.subList(info.parameterOffset, info.parameterOffset + info.parameterCount));
                    }
                }

                if (trivialWhereClause) {
                    componentParameters.add(parameters.get(parameters.size() - 1));
                    componentParamNames.add(paramNames.get(paramNames.size() - 1));
                }

                queries.add(new ParsedPSJ(componentRelations, componentHasRelAlias, componentRelAliasToIdx, componentProjectColumns, componentParameters,
                        componentParamNames, componentTheta, trivialWhereClause).getSolverQuery(schema, prefix, parameterOffset));
            }

            return queries;
        }

        @Override
        protected BoolExpr predicateGenerator(Tuple... tuples) {
            Map<String, Expr> map = new HashMap<>();
            for (int i = 0; i < thetaColumnIndex.length; ++i) {
                map.put(thetaColumns.get(i), tuples[thetaRelationIndex[i]].get(thetaColumnIndex[i]));
            }
            return getPredicate(map, schema, prefix, parameterOffset);
        }

        @Override
        protected Tuple headSelector(Tuple... tuples) {
            Expr[] parts = new Expr[projectRelationIndex.length];
            for (int i = 0; i < parts.length; ++i) {
                parts[i] = tuples[projectRelationIndex[i]].get(projectColumnIndex[i]);
            }
            return new Tuple(schema, parts);
        }

        @Override
        protected Sort[] headTypeSelector(Sort[]... types) {
            Sort[] parts = new Sort[projectRelationIndex.length];
            for (int i = 0; i < parts.length; ++i) {
                parts[i] = types[projectRelationIndex[i]][projectColumnIndex[i]];
            }
            return parts;
        }

        @Override
        public Schema getSchema() {
            return schema;
        }
    }
}
