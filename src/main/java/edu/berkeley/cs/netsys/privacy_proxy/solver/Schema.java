package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ListMultimap;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.sql.SchemaPlusWithKey;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeFamily;
import org.apache.calcite.rel.type.RelDataTypeField;
import org.apache.calcite.sql.type.SqlTypeFamily;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class Schema<C extends Z3ContextWrapper<?, ?, ?, ?>> {
    private final C context;
    private final SchemaPlusWithKey rawSchema;
    private final ImmutableMap<String, ImmutableList<Column>> relations;
    private final List<Dependency> dependencies;

    private final LoadingCache<ImmutableList<Policy>, ImmutableList<Query<C>>> policyQueries;

    public Schema(C context, SchemaPlusWithKey rawSchema, List<Dependency> dependencies) {
        this.context = checkNotNull(context);
        this.rawSchema = checkNotNull(rawSchema);
        this.dependencies = checkNotNull(dependencies);

        ImmutableMap.Builder<String, ImmutableList<Column>> relationsBuilder = new ImmutableMap.Builder<>();
        for (String tableName : rawSchema.schema.getTableNames()) {
            ImmutableList.Builder<Column> columnsBuilder = new ImmutableList.Builder<>();
            for (RelDataTypeField field : rawSchema.getTypeForTable(tableName).getFieldList()) {
                Sort type = getSortFromSqlType(context, field.getType());
                // TODO(zhangwen): Other parts of the code seem to assume upper case table and column names (see
                //  ParsedPSJ.quantifyName), and so we upper case the column and table names here.  I hope this works.
                columnsBuilder.add(new Column(field.getName().toUpperCase(), type));
            }
            relationsBuilder.put(tableName.toUpperCase(), columnsBuilder.build());
        }
        this.relations = relationsBuilder.build();

        this.policyQueries = CacheBuilder.newBuilder().maximumSize(1).build(
                new CacheLoader<>() {
                    @Override
                    public ImmutableList<Query<C>> load(ImmutableList<Policy> policies) {
                        return policies.stream().map(p -> p.getSolverQuery(Schema.this))
                                .collect(ImmutableList.toImmutableList());
                    }
                }
        );
    }

    public ImmutableList<Query<C>> getPolicyQueries(ImmutableList<Policy> policies) {
        return policyQueries.getUnchecked(policies);
    }

    private static Sort getSortFromSqlType(Z3ContextWrapper<?, ?, ?, ?> context, RelDataType type) {
        RelDataTypeFamily family = type.getFamily();
        if (family == SqlTypeFamily.NUMERIC) {
            // TODO(zhangwen): treating decimal also as int.
            switch (type.getSqlTypeName()) {
                case TINYINT:
                case SMALLINT:
                case INTEGER:
                case BIGINT:
                    return context.getCustomIntSort();
                case FLOAT:
                case REAL:
                case DOUBLE:
                    return context.getCustomRealSort();
            }
            throw new IllegalArgumentException("Unsupported numeric type: " + type);
        } else if (family == SqlTypeFamily.CHARACTER || family == SqlTypeFamily.BINARY) {
            return context.getCustomStringSort();
        } else if (family == SqlTypeFamily.TIMESTAMP) {
            return context.getTimestampSort();
        } else if (family == SqlTypeFamily.DATE) {
            return context.getDateSort();
        } else if (family == SqlTypeFamily.BOOLEAN) {
            return context.getCustomBoolSort();
        } else if (family == SqlTypeFamily.ANY) {
            // FIXME(zhangwen): I think text belongs in here.
            return context.getCustomStringSort();
        }
        throw new IllegalArgumentException("unrecognized family: " + family);
    }

    public C getContext() {
        return context;
    }

    public List<Dependency> getDependencies() {
        return dependencies;
    }

    public Instance<C> makeFreshInstance(String instancePrefix) {
        Instance.Builder<C> instBuilder = new Instance.Builder<>(instancePrefix, this);
        for (ImmutableMap.Entry<String, ImmutableList<Column>> relation : relations.entrySet()) {
            String relationName = relation.getKey();
            List<Column> columns = relation.getValue();

            Sort[] colTypes = columns.stream().map(Column::type).toArray(Sort[]::new);
            FuncDecl<BoolSort> func = context.mkFreshFuncDecl(instancePrefix + "_" + relationName, colTypes,
                    context.getBoolSort());
            instBuilder.put(relationName, new GeneralRelation<>(this, new Z3Function(func), colTypes));
        }
        return instBuilder.buildUnbounded();
    }

    /**
     * Creates a bounded database instance of this schema.
     * @param instancePrefix identifies this instance.
     * @param bounds maps table name to upper bound on size (number of rows).
     * @param table2KnownRows maps table name to distinct known partial rows of the table; each row is represented as
     *                        a map from column name to value.
     * @return a concrete instance.
     */
    public BoundedInstance<C> makeBoundedInstance(String instancePrefix, Map<String, Integer> bounds,
                                           ListMultimap<String, Map<String, Object>> table2KnownRows) {
        Instance.Builder<C> instBuilder = new Instance.Builder<>(instancePrefix, this);
        for (ImmutableMap.Entry<String, ImmutableList<Column>> relation : relations.entrySet()) {
            String relationName = relation.getKey();
            List<Column> columns = relation.getValue();
            Sort[] colTypes = columns.stream().map(Column::type).toArray(Sort[]::new);

            int numTuples = bounds.get(relationName);
            ArrayList<Tuple<C>> tuples = new ArrayList<>();
            ArrayList<BoolExpr> exists = new ArrayList<>();
            String prefix = instancePrefix + "_" + relationName;

            List<Map<String, Object>> knownRows =
                    table2KnownRows == null ? Collections.emptyList() : table2KnownRows.get(relationName);
            checkArgument(knownRows.size() <= numTuples,
                    String.format("table %s has %d known rows specified, more than bound %d",
                            relationName, knownRows.size(), numTuples));

            int i = 0;
//            System.out.println("***\t" + relationName);
            for (Map<String, Object> knownRow : knownRows) {
                List<Expr<?>> values = new ArrayList<>();
                for (Column col : columns) {
                    Object knownValue = knownRow.get(col.name());
                    if (knownValue != null) {
                        // TODO(zhangwen): This ignores a known NULL value, which is safe to do; fix?
                        values.add(context.getExprForValue(knownValue));
                    } else {
                        Expr<?> thisVar = context.mkConst(prefix + "_" + i + "_" + col.name(), col.type());
                        instBuilder.addDbVar(thisVar);
                        values.add(thisVar);
                    }
                }
                tuples.add(new Tuple<>(this, values.stream()));
//                System.out.println("***\t" + tuples[i]);
                exists.add(context.mkTrue()); // A tuple with a known PK value must exist.
                i += 1;
            }

            for (; i < numTuples; ++i) {
                List<Expr<?>> values = new ArrayList<>();
                for (Column col : columns) {
                    Expr<?> thisVar = context.mkConst(prefix + "_" + i + "_" + col.name(), col.type());
                    instBuilder.addDbVar(thisVar);
                    values.add(thisVar);
                }
                tuples.add(new Tuple<>(this, values));

                BoolExpr existsVar = context.mkBoolConst(prefix + "_" + i + "_exists");
                instBuilder.addDbVar(existsVar);
                exists.add(existsVar);
            }
            instBuilder.put(relationName, new ConcreteRelation<>(this, colTypes, tuples, exists));
        }
        return instBuilder.buildBounded();
    }

    public Instance<C> makeBoundedInstance(String instancePrefix, Map<String, Integer> bounds) {
        return makeBoundedInstance(instancePrefix, bounds, null);
    }

    public List<String> getRelationNames() {
        return rawSchema.getRelationNames();
    }

    public List<Column> getColumns(String relationName) {
        return relations.get(relationName.toUpperCase());
    }

    private final Map<String, List<String>> columnNamesCache = new HashMap<>();
    public List<String> getColumnNames(String relationName) {
        return columnNamesCache.computeIfAbsent(
                relationName,
                k -> relations.get(k).stream().map(Column::name).collect(Collectors.toList())
        );
    }

    public Tuple<C> makeFreshQuantifiedTuple(String relationName) {
        return makeFreshQuantifiedTuple(relationName, "e");
    }

    public Tuple<C> makeFreshQuantifiedTuple(String relationName, String prefix) {
        List<Column> columns = relations.get(relationName.toUpperCase());
        return new Tuple<>(this, columns.stream()
                .map(column -> context.mkFreshQuantifiedConst(prefix, column.type())));
    }

    public SchemaPlusWithKey getRawSchema() {
        return rawSchema;
    }
}
