package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Sort;

import java.util.Collections;
import java.util.List;

import static com.google.common.base.Preconditions.*;

public record ForeignKeyDependency(String fromRelation, String fromColumn,
                                   String toRelation, String toColumn) implements Dependency {
    public ForeignKeyDependency(String fromRelation, String fromColumn, String toRelation, String toColumn) {
        this.fromRelation = checkNotNull(fromRelation);
        this.fromColumn = checkNotNull(fromColumn);
        this.toRelation = checkNotNull(toRelation);
        this.toColumn = checkNotNull(toColumn);
    }

    @Override
    public Iterable<BoolExpr> apply(Instance instance) {
        Schema schema = instance.getSchema();
        int fromIndex = schema.getColumnNames(fromRelation).indexOf(fromColumn);
        checkArgument(fromIndex >= 0);
        int toIndex = schema.getColumnNames(toRelation).indexOf(toColumn);
        checkArgument(toIndex >= 0);
        PSJ selectFromQuery = new PSJ(schema, Collections.singletonList(fromRelation)) {
            @Override
            protected Tuple headSelector(Tuple... tuples) {
                return new Tuple(getSchema(), tuples[0].get(fromIndex));
            }

            @Override
            protected Sort[] headTypeSelector(Sort[]... types) {
                return new Sort[]{types[0][fromIndex]};
            }
        };
        PSJ selectToQuery = new PSJ(schema, Collections.singletonList(toRelation)) {
            @Override
            protected Tuple headSelector(Tuple... tuples) {
                return new Tuple(getSchema(), tuples[0].get(toIndex));
            }

            @Override
            protected Sort[] headTypeSelector(Sort[]... types) {
                return new Sort[]{types[0][toIndex]};
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
