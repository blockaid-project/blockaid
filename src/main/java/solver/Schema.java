package solver;

import com.microsoft.z3.*;

import java.sql.Types;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Schema {
    private Map<String, List<Column>> relations;
    private List<Dependency> dependencies;

    public Schema(Map<String, List<Column>> relations) {
        this(relations, Collections.emptyList());
    }

    public Schema(Map<String, List<Column>> relations, List<Dependency> dependencies) {
        this.relations = relations;
        this.dependencies = dependencies;
    }

    public Instance makeFreshInstance(Context context) {
        Instance instance = new Instance(this);
        List<BoolExpr> constraints = new ArrayList<>();
        for (Map.Entry<String, List<Column>> relation : relations.entrySet()) {
            String relationName = relation.getKey();
            List<Column> columns = relation.getValue();

            Sort[] colTypes = columns.stream().map(column -> column.type).toArray(Sort[]::new);
            FuncDecl func = context.mkFreshFuncDecl("v", colTypes, context.getBoolSort());
            instance.put(relationName, new Relation(new Z3Function(func), colTypes));

            // Apply per-column constraints.
            Tuple tuple = this.makeFreshTuple(context, relationName);
            List<BoolExpr> thisConstraints = new ArrayList<>();
            for (int i = 0; i < tuple.size(); ++i) {
                Column column = columns.get(i);
                if (column.constraint == null) {
                    continue;
                }
                thisConstraints.add(column.constraint.apply(context, tuple.get(i)));
            }
            if (!thisConstraints.isEmpty()) {
                BoolExpr lhs = (BoolExpr) func.apply(tuple.toArray(new Expr[0]));
                BoolExpr rhs = context.mkAnd(thisConstraints.toArray(new BoolExpr[0]));
                BoolExpr body = context.mkImplies(lhs, rhs);
                constraints.add(context.mkForall(tuple.toArray(new Expr[0]), body, 1, null, null, null, null));
            }
        }

        // Apply dependencies.
        for (Dependency d : dependencies) {
            constraints.add(d.apply(context, instance));
        }

        instance.constraint = context.mkAnd(constraints.toArray(new BoolExpr[0]));
        return instance;
    }

    public Instance makeConcreteInstance(Context context, Map<String, List<Tuple>> content) {
        Instance instance = this.makeFreshInstance(context);
        List<BoolExpr> constraints = new ArrayList<>();
        constraints.add(instance.constraint);
        for (Map.Entry<String, List<Tuple>> c : content.entrySet()) {
            String relationName = c.getKey();
            List<Tuple> tuples = c.getValue();

            Tuple tuple = this.makeFreshTuple(context, relationName);
            BoolExpr lhs = instance.get(relationName).apply(tuple.toArray(new Expr[0]));
            Stream<BoolExpr> rhsExprs = tuples.stream().map((t) -> tuple.tupleEqual(context, t));
            BoolExpr rhs = context.mkOr(rhsExprs.toArray(BoolExpr[]::new));
            BoolExpr body = context.mkEq(lhs, rhs);
            constraints.add(context.mkForall(tuple.toArray(new Expr[0]), body, 1, null, null, null, null));
        }
        instance.constraint = context.mkAnd(constraints.toArray(new BoolExpr[0]));
        return instance;
    }

    public List<Column> getColumns(String relationName) {
        return relations.get(relationName.toUpperCase());
    }

    private Map<String, List<String>> columnNamesCache = new HashMap<>();
    public List<String> getColumnNames(String relationName) {
        return columnNamesCache.computeIfAbsent(
                relationName,
                k -> relations.get(k).stream().map(c -> c.name).collect(Collectors.toList())
        );
    }

    public Tuple makeFreshTuple(Context context, String relationName) {
        List<Column> columns = relations.get(relationName.toUpperCase());
        Tuple tuple = new Tuple();
        for (Column column : columns) {
            tuple.add(context.mkFreshConst("v", column.type));
        }
        return tuple;
    }

    public static Sort getSortFromSqlType(Context context, int type) {
        switch (type) {
            case Types.INTEGER:
                return context.getIntSort();
            case Types.DOUBLE:
                return context.getRealSort();
            case Types.BOOLEAN:
                return context.getBoolSort();
            case Types.CLOB:
                return context.getStringSort();
            case Types.TIMESTAMP: // TODO
            case Types.DATE:
                return context.getStringSort();
            default:
                throw new UnsupportedOperationException("bad column type: " + type);
        }
    }
}
