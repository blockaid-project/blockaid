package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Sets;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.sql.SchemaPlusWithKey;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeField;
import org.apache.calcite.sql.type.SqlTypeName;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class Schema<C extends Z3ContextWrapper<?, ?, ?, ?>> {
    private final C context;
    private final SchemaPlusWithKey rawSchema;
    private final ImmutableMap<String, ImmutableList<Column>> relations;
    private final ImmutableList<Dependency> dependencies;

    private final LoadingCache<ImmutableList<Policy>, ImmutableList<Query<C>>> policyQueries;

    public Schema(C context, SchemaPlusWithKey rawSchema, List<Dependency> dependencies) {
        this.context = checkNotNull(context);
        this.rawSchema = checkNotNull(rawSchema);

        ImmutableList.Builder<Dependency> dependenciesBuilder = new ImmutableList.Builder<>();
        dependenciesBuilder.addAll(dependencies);

        ImmutableMap.Builder<String, ImmutableList<Column>> relationsBuilder = new ImmutableMap.Builder<>();
        for (String tableName : rawSchema.schema.getTableNames()) {
            ImmutableList.Builder<Column> columnsBuilder = new ImmutableList.Builder<>();
            for (RelDataTypeField field : rawSchema.getTypeForTable(tableName).getFieldList()) {
                String fieldName = field.getName().toUpperCase();
                RelDataType dataType = field.getType();
                SqlTypeName typeName = dataType.getSqlTypeName();

                Z3ContextWrapper.Nullability nullability;
                if (dataType.isNullable()) {
                    nullability = Z3ContextWrapper.Nullability.IS_NULLABLE;
                } else {
                    nullability = Z3ContextWrapper.Nullability.NOT_NULLABLE;
                    dependenciesBuilder.add(new NotNullDependency(tableName.toUpperCase(), fieldName));
                }

                Sort sort = context.getSortFromSqlType(typeName, nullability);
                // TODO(zhangwen): Other parts of the code seem to assume upper case table and column names (see
                //  ParsedPSJ.quantifyName), and so we upper case the column and table names here.  I hope this works.
                columnsBuilder.add(new Column(fieldName, sort));
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

        this.dependencies = dependenciesBuilder.build();
    }

    public ImmutableList<Query<C>> getPolicyQueries(ImmutableList<Policy> policies) {
        return policyQueries.getUnchecked(policies);
    }

    public C getContext() {
        return context;
    }

    public ImmutableList<Dependency> getDependencies() {
        return dependencies;
    }

    public Instance<C> makeUnboundedInstance(String name) {
        Instance.Builder<C> instBuilder = new Instance.Builder<>(this);
        for (ImmutableMap.Entry<String, ImmutableList<Column>> relation : relations.entrySet()) {
            String relationName = relation.getKey();
            List<Column> columns = relation.getValue();

            ImmutableList<Sort> colTypes = columns.stream().map(Column::type).collect(ImmutableList.toImmutableList());
            FuncDecl<BoolSort> func = context.mkFuncDecl(name + "_" + relationName,
                    colTypes.toArray(new Sort[0]), context.getBoolSort());
            instBuilder.put(relationName, new GeneralRelation<>(this, new Z3Function(func), colTypes));
        }
        return instBuilder.buildUnbounded();
    }

    /**
     * Creates a bounded database instance of this schema.
     * @param name identifies this instance.
     * @param bounds maps table name to upper bound on size (number of rows).
     * @param table2KnownRows maps table name to distinct known partial rows of the table; each row is represented as
     *                        a map from column name to value.
     * @return a concrete instance.
     */
    public BoundedInstance<C> makeBoundedInstance(String name, Map<String, Integer> bounds,
                                                  ListMultimap<String, Map<String, Object>> table2KnownRows) {
        Instance.Builder<C> instBuilder = new Instance.Builder<>(this);
        for (ImmutableMap.Entry<String, ImmutableList<Column>> relation : relations.entrySet()) {
            String relationName = relation.getKey();
            List<Column> columns = relation.getValue();
            ImmutableList<Sort> colTypes = columns.stream().map(Column::type).collect(ImmutableList.toImmutableList());

            int numTuples = bounds.get(relationName);
            ArrayList<Tuple<C>> tuples = new ArrayList<>();
            ArrayList<BoolExpr> exists = new ArrayList<>();
            String prefix = name + "_" + relationName;

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
                tuples.add(new Tuple<>(this, values));
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

    /**
     * Computes the relevant tables for a trace.  The set of relevant tables is the minimal set that satisfies:
     * - A table that appears in the trace (either previous or current query) is relevant.
     * - In a constraint `LHS \subseteq RHS`, if LHS references a relevant table, then all tables referenced by RHS
     *   are relevant.
     *
     * @param trace the trace to compute relevant tables from.
     * @return the set of relevant table names.
     */
    public Set<String> computeRelevantTables(UnmodifiableLinearQueryTrace trace) {
        HashSet<String> relevantTables = new HashSet<>();
        for (QueryTraceEntry entry : trace.getAllEntries()) { // This includes the current query as well.
            relevantTables.addAll(entry.getQuery().getRelations());
        }

        boolean converged;
        do {
            converged = true;
            for (Dependency d : dependencies) {
                if (Sets.intersection(d.getFromRelations(), relevantTables).isEmpty()) {
                    continue;
                }
                if (relevantTables.containsAll(d.getToRelations())) {
                    continue;
                }
                converged = false;
                relevantTables.addAll(d.getToRelations());
            }
        } while (!converged);

        return relevantTables;
    }
}
