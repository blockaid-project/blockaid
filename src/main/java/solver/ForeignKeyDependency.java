package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Sort;

import java.util.Collections;
import java.util.Objects;

import static com.google.common.base.Preconditions.*;

public class ForeignKeyDependency implements Dependency {
    private final String fromRelation;
    private final String fromColumn;
    private final String toRelation;
    private final String toColumn;

    public ForeignKeyDependency(String fromRelation, String fromColumn, String toRelation, String toColumn) {
        this.fromRelation = checkNotNull(fromRelation);
        this.fromColumn = checkNotNull(fromColumn);
        this.toRelation = checkNotNull(toRelation);
        this.toColumn = checkNotNull(toColumn);
    }

    @Override
    public BoolExpr apply(Instance instance) {
        Schema schema = instance.schema;
        int fromIndex = schema.getColumnNames(fromRelation).indexOf(fromColumn);
        checkArgument(fromIndex >= 0);
        int toIndex = schema.getColumnNames(toRelation).indexOf(toColumn);
        checkArgument(toIndex >= 0);
        PSJ selectFromQuery = new PSJ(schema, Collections.singletonList(fromRelation)) {
            @Override
            protected Tuple headSelector(Tuple... tuples) {
                return new Tuple(schema, tuples[0].get(fromIndex));
            }
            @Override
            protected Sort[] headTypeSelector(Sort[]... types) {
                return new Sort[] { types[0][fromIndex] };
            }
        };
        PSJ selectToQuery = new PSJ(schema, Collections.singletonList(toRelation)) {
            @Override
            protected Tuple headSelector(Tuple... tuples) {
                return new Tuple(schema, tuples[0].get(toIndex));
            }
            @Override
            protected Sort[] headTypeSelector(Sort[]... types) {
                return new Sort[] { types[0][toIndex] };
            }
        };
        return selectFromQuery.apply(instance).isContainedIn(selectToQuery.apply(instance));
    }

    @Override
    public String toString() {
        return "ForeignKeyDependency{" +
                "fromRelation='" + fromRelation + '\'' +
                ", fromColumn='" + fromColumn + '\'' +
                ", toRelation='" + toRelation + '\'' +
                ", toColumn='" + toColumn + '\'' +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ForeignKeyDependency that = (ForeignKeyDependency) o;
        return fromRelation.equals(that.fromRelation) && fromColumn.equals(that.fromColumn) && toRelation.equals(that.toRelation) && toColumn.equals(that.toColumn);
    }

    @Override
    public int hashCode() {
        return Objects.hash(fromRelation, fromColumn, toRelation, toColumn);
    }
}
