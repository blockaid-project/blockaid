package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Sort;

import java.util.Collections;

public class ForeignKeyDependency implements Dependency {
    private final String fromRelation;
    private final String fromColumn;
    private final String toRelation;
    private final String toColumn;

    public ForeignKeyDependency(String fromRelation, String fromColumn, String toRelation, String toColumn) {
        this.fromRelation = fromRelation;
        this.fromColumn = fromColumn;
        this.toRelation = toRelation;
        this.toColumn = toColumn;
    }

    @Override
    public BoolExpr apply(Instance instance) {
        Schema schema = instance.schema;
        int fromIndex = schema.getColumnNames(fromRelation).indexOf(fromColumn);
        int toIndex = schema.getColumnNames(toRelation).indexOf(toColumn);
        PSJ selectFromRelation = new PSJ(schema, Collections.singletonList(fromRelation)) {
            @Override
            protected Tuple headSelector(Tuple... tuples) {
                return new Tuple(schema, tuples[0].get(fromIndex));
            }
            @Override
            protected Sort[] headTypeSelector(Sort[]... types) {
                return new Sort[] { types[0][fromIndex] };
            }
        };
        PSJ selectToRelation = new PSJ(schema, Collections.singletonList(toRelation)) {
            @Override
            protected Tuple headSelector(Tuple... tuples) {
                return new Tuple(schema, tuples[0].get(toIndex));
            }
            @Override
            protected Sort[] headTypeSelector(Sort[]... types) {
                return new Sort[] { types[0][toIndex] };
            }
        };
        return selectFromRelation.apply(instance).isContainedIn(selectToRelation.apply(instance));
    }
}
