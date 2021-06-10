package solver;

import com.microsoft.z3.*;

import java.sql.Types;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkNotNull;

public class Schema {
    private final MyZ3Context context;
    private final Map<String, List<Column>> relations;
    private final List<Dependency> dependencies;

    public Schema(MyZ3Context context, Map<String, List<Column>> relations, List<Dependency> dependencies) {
        this.context = checkNotNull(context);
        this.relations = checkNotNull(relations);
        this.dependencies = checkNotNull(dependencies);
    }

    public MyZ3Context getContext() {
        return context;
    }

    public Instance makeFreshInstance() {
        Instance instance = new Instance(this);
        List<BoolExpr> constraints = new ArrayList<>();
        for (Map.Entry<String, List<Column>> relation : relations.entrySet()) {
            String relationName = relation.getKey();
            List<Column> columns = relation.getValue();

            Sort[] colTypes = columns.stream().map(column -> column.type).toArray(Sort[]::new);
            FuncDecl func = context.mkFreshFuncDecl("v", colTypes, context.getBoolSort());
            instance.put(relationName, new GeneralRelation(this, new Z3Function(func), colTypes));
        }

        // Apply dependencies.
        for (Dependency d : dependencies) {
            constraints.add(d.apply(instance));
        }

        instance.constraint = context.mkAnd(constraints.toArray(new BoolExpr[0]));
        return instance;
    }

    public Instance makeConcreteInstance(String instancePrefix, Map<String, Integer> bounds) {
        Instance instance = new Instance(this, true);
        List<BoolExpr> constraints = new ArrayList<>();
        for (Map.Entry<String, List<Column>> relation : relations.entrySet()) {
            String relationName = relation.getKey();
            List<Column> columns = relation.getValue();
            Sort[] colTypes = columns.stream().map(column -> column.type).toArray(Sort[]::new);

            Tuple[] tuples = new Tuple[bounds.get(relationName)];
            BoolExpr[] exists = new BoolExpr[bounds.get(relationName)];
            String prefix = instancePrefix + "_" + relationName;
            for (int i = 0; i < tuples.length; ++i) {
                List<Expr> values = new ArrayList<>();
                for (int j = 0; j < colTypes.length; ++j) {
                    values.add(context.mkConst(prefix + "_" + i + "_" + j, colTypes[j]));
                }
                tuples[i] = new Tuple(this, values.stream());
                exists[i] = context.mkBoolConst(prefix + "_" + i + "_exists");
            }
            instance.put(relationName, new ConcreteRelation(this, colTypes, tuples, exists));
        }

        for (Dependency d : dependencies) {
            constraints.add(d.apply(instance));
        }

        instance.constraint = context.mkAnd(constraints.toArray(new BoolExpr[0]));
        return instance;
    }

    public List<Column> getColumns(String relationName) {
        return relations.get(relationName.toUpperCase());
    }

    private final Map<String, List<String>> columnNamesCache = new HashMap<>();
    public List<String> getColumnNames(String relationName) {
        return columnNamesCache.computeIfAbsent(
                relationName,
                k -> relations.get(k).stream().map(c -> c.name).collect(Collectors.toList())
        );
    }

    public Tuple makeFreshTuple(String relationName) {
        List<Column> columns = relations.get(relationName.toUpperCase());
        return new Tuple(this, columns.stream().map(column -> context.mkFreshConst("v", column.type)));
    }

    public static Sort getSortFromSqlType(Context context, int type) {
        switch (type) {
            case Types.INTEGER:
            case Types.BIGINT:
            case Types.TINYINT:
                return context.getIntSort();
            case Types.DOUBLE:
                return context.getRealSort();
            case Types.BOOLEAN:
                return context.getBoolSort();
            case Types.VARCHAR:
            case Types.LONGVARCHAR:
            case Types.CLOB:
                return context.getStringSort();
            case Types.TIMESTAMP:
            case Types.DATE:
                return context.getIntSort();
            default:
                throw new UnsupportedOperationException("bad column type: " + type);
        }
    }
}
