package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.BoolExpr;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.Collections;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;

/**
 * That a column of a table is not null.
 * TODO(zhangwen): not a "dependency"?
 */
public record NotNullDependency(String relationName, String columnName) implements Dependency {
    @Override
    public <C extends Z3ContextWrapper<?, ?, ?, ?>> Iterable<BoolExpr> apply(Instance<C> instance) {
        Schema<C> schema = instance.getSchema();
        int colIndex = schema.getColumnNames(relationName).indexOf(columnName);
        checkArgument(colIndex >= 0, "cannot find column " + columnName + " in relation " + relationName);

        // SELECT (nothing) FROM relationName WHERE relationName.columnName IS NULL
        PSJ<C> selectNullQuery = new PSJ<>(schema, List.of(relationName)) {
            @Override
            protected BoolExpr predicateGenerator(List<Tuple<C>> tuples) {
                checkArgument(tuples.size() == 1); // The query `SELECT`s from one table.
                Tuple<C> tuple = tuples.get(0);
                return schema.getContext().mkSqlIsNull(tuple.get(colIndex));
            }

            @Override
            protected List<RelationColumnPair> headSelector() {
                return Collections.emptyList();
            }
        };

        return selectNullQuery.apply(instance).isEmptyExpr();
    }

    @Override
    public List<String> getRelevantColumns() {
        // TODO(zhangwen): is this column even relevant?
        return List.of(
                (relationName + "." + columnName).toUpperCase()
        );
    }

    @Override
    public ImmutableSet<String> getFromRelations() {
        return ImmutableSet.of(relationName);
    }

    @Override
    public ImmutableSet<String> getToRelations() {
        return ImmutableSet.of();
    }

    @Override
    public ImmutableSet<String> getCriticalRelations() {
        return ImmutableSet.of(relationName);
    }
}
