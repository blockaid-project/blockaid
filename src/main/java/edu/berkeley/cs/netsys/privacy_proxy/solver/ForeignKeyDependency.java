package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.BoolExpr;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.List;

import static com.google.common.base.Preconditions.*;

/**
 * A foreign key dependency from one column to another.  Applies only to non-null values in the "from" column.
 */
public record ForeignKeyDependency(
        String fromRelation, String fromColumn, String toRelation, String toColumn) implements Dependency {
    public ForeignKeyDependency(String fromRelation, String fromColumn, String toRelation, String toColumn) {
        this.fromRelation = checkNotNull(fromRelation);
        this.fromColumn = checkNotNull(fromColumn);
        this.toRelation = checkNotNull(toRelation);
        this.toColumn = checkNotNull(toColumn);
    }

    @Override
    public <C extends Z3ContextWrapper<?, ?, ?, ?>> Iterable<BoolExpr> apply(Instance<C> instance) {
        Schema<C> schema = instance.getSchema();
        int fromColIndex = schema.getColumnNames(fromRelation).indexOf(fromColumn);
        checkArgument(fromColIndex >= 0);
        int toColIndex = schema.getColumnNames(toRelation).indexOf(toColumn);
        checkArgument(toColIndex >= 0);
        PSJ<C> selectFromQuery = new PSJ<>(schema, List.of(fromRelation)) {
            @Override
            protected BoolExpr predicateGenerator(List<Tuple<C>> tuples) {
                checkArgument(tuples.size() == 1); // The query `SELECT`s from one table.
                Tuple<C> tuple = tuples.get(0);
                return schema.getContext().mkSqlIsNotNull(tuple.get(fromColIndex));
            }

            @Override
            protected List<RelationColumnPair> headSelector() {
                return List.of(new RelationColumnPair(0, fromColIndex));
            }
        };
        PSJ<C> selectToQuery = new PSJ<>(schema, List.of(toRelation)) {
            @Override
            protected BoolExpr predicateGenerator(List<Tuple<C>> tuples) {
                return schema.getContext().mkTrue();
            }

            @Override
            protected List<RelationColumnPair> headSelector() {
                return List.of(new RelationColumnPair(0, toColIndex));
            }
        };
        return selectFromQuery.apply(instance).isContainedInExpr(selectToQuery.apply(instance));
    }

    @Override
    public List<String> getRelevantColumns() {
        return List.of(
                (fromRelation + "." + fromColumn).toUpperCase(),
                (toRelation + "." + toColumn).toUpperCase()
        );
    }

    @Override
    public ImmutableSet<String> getFromRelations() {
        return ImmutableSet.of(fromRelation);
    }

    @Override
    public ImmutableSet<String> getToRelations() {
        return ImmutableSet.of(toRelation);
    }
}
