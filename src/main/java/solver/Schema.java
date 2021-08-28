package solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.SetMultimap;
import com.microsoft.z3.*;
import org.apache.calcite.schema.SchemaPlus;
import sql.SchemaPlusWithKey;

import java.sql.Types;
import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class Schema {
    private final MyZ3Context context;
    private final SchemaPlusWithKey rawSchema;
    private final Map<String, List<Column>> relations;
    private final List<Constraint> dependencies;

    public Schema(MyZ3Context context, SchemaPlusWithKey rawSchema, Map<String, List<Column>> relations,
                  List<Constraint> dependencies) {
        this.context = checkNotNull(context);
        this.rawSchema = checkNotNull(rawSchema);
        this.relations = checkNotNull(relations);
        this.dependencies = checkNotNull(dependencies);
    }

    public MyZ3Context getContext() {
        return context;
    }

    public List<Constraint> getDependencies() {
        return dependencies;
    }

    public Instance makeFreshInstance(String instancePrefix) {
        Instance instance = new Instance(this, false);
        Map<Constraint, BoolExpr> constraints = new HashMap<>();
        for (Map.Entry<String, List<Column>> relation : relations.entrySet()) {
            String relationName = relation.getKey();
            List<Column> columns = relation.getValue();

            Sort[] colTypes = columns.stream().map(column -> column.type).toArray(Sort[]::new);
            FuncDecl func = context.mkFreshFuncDecl(instancePrefix + "_" + relationName, colTypes,
                    context.getBoolSort());
            instance.put(relationName, new GeneralRelation(this, new Z3Function(func), colTypes));
        }

        // Apply dependencies.
        for (Constraint d : dependencies) {
            constraints.put(d, d.apply(instance));
        }

        instance.setConstraints(constraints);
        return instance;
    }

    public Instance makeConcreteInstance(String instancePrefix, Map<String, Integer> bounds,
                                         SetMultimap<String, Object> table2pkValues) {
        Instance instance = new Instance(this, true);
        for (Map.Entry<String, List<Column>> relation : relations.entrySet()) {
            String relationName = relation.getKey();
            List<Column> columns = relation.getValue();
            Sort[] colTypes = columns.stream().map(column -> column.type).toArray(Sort[]::new);

            int numTuples = bounds.get(relationName);
            Tuple[] tuples = new Tuple[numTuples];
            BoolExpr[] exists = new BoolExpr[numTuples];
            String prefix = instancePrefix + "_" + relationName;

            Set<Object> pkValues = table2pkValues == null ? Collections.emptySet() : table2pkValues.get(relationName);
            ImmutableList<String> pkColumnNames = rawSchema.getPrimaryKeyColumns(relationName);
            String pkColumnName;
            if (pkColumnNames == null || pkColumnNames.size() != 1) {
                // The primary-key optimization is only supported if the table has exactly one primary-key column.
                pkColumnName = null;
            } else {
                pkColumnName = pkColumnNames.get(0);

                String finalPkColumnName = pkColumnName;
                long count = columns.stream().filter(col -> col.name.equals(finalPkColumnName)).count();
                checkArgument(count == 1,
                        "table " + relationName + " contains " + count
                                + " copies of PK column " + pkColumnName);
            }

            checkArgument(pkValues.size() <= numTuples,
                    String.format("table %s has %d primary keys specified, more than bound %d",
                            relationName, pkValues.size(), numTuples));

            int i = 0;
            for (Object pkValue : pkValues) {
                List<Expr> values = new ArrayList<>();
                for (Column col : columns) {
                    if (col.name.equals(pkColumnName)) {
                        values.add(Tuple.getExprFromObject(context, pkValue));
                    } else {
                        values.add(context.mkConst(prefix + "_" + i + "_" + col.name, col.type));
                    }
                }
                tuples[i] = new Tuple(this, values.stream());
                exists[i] = context.mkTrue(); // A tuple with a known PK value must exist.
                i += 1;
            }

            for (; i < numTuples; ++i) {
                List<Expr> values = new ArrayList<>();
                for (Column col : columns) {
                    values.add(context.mkConst(prefix + "_" + i + "_" + col.name, col.type));
                }
                tuples[i] = new Tuple(this, values.stream());
                exists[i] = context.mkBoolConst(prefix + "_" + i + "_exists");
            }
            instance.put(relationName, new ConcreteRelation(this, colTypes, tuples, exists));
        }

        Map<Constraint, BoolExpr> constraints = new HashMap<>();
        for (Constraint d : dependencies) {
            constraints.put(d, d.apply(instance));
        }
        instance.setConstraints(constraints);
        return instance;
    }

    public Instance makeConcreteInstance(String instancePrefix, Map<String, Integer> bounds) {
        return makeConcreteInstance(instancePrefix, bounds, null);
    }

    public List<String> getRelationNames() {
        return relations.keySet().stream().map(String::toUpperCase).collect(Collectors.toList());
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

    public static Sort getSortFromSqlType(MyZ3Context context, int type) {
        switch (type) {
            case Types.INTEGER:
            case Types.BIGINT:
            case Types.TINYINT:
                return context.getCustomIntSort();
            case Types.REAL:
            case Types.DOUBLE:
                return context.getCustomRealSort();
            case Types.BOOLEAN:
                return context.getBoolSort();
            case Types.VARCHAR:
            case Types.LONGVARCHAR:
            case Types.CLOB:
            case Types.LONGVARBINARY:
                return context.getCustomStringSort();
            case Types.TIMESTAMP:
                return context.getTimestampSort();
            case Types.DATE:
                return context.getDateSort();
            default:
                throw new UnsupportedOperationException("bad column type: " + type);
        }
    }

    public SchemaPlusWithKey getRawSchema() {
        return rawSchema;
    }
}
