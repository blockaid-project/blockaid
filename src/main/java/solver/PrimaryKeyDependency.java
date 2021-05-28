package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;

import java.util.*;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;

public class PrimaryKeyDependency implements Dependency {
    private final String relationName;
    private final Set<String> columnNames;

    public PrimaryKeyDependency(String relationName, Collection<String> columnNames) {
        this.relationName = relationName;
        checkArgument(!columnNames.isEmpty());
        this.columnNames = new HashSet<>(columnNames);
    }

    @Override
    public BoolExpr apply(Instance instance) {
        Context context = instance.getContext();

        Relation relation = instance.get(this.relationName);
        Schema schema = instance.schema;
        Tuple tup1 = schema.makeFreshTuple(relationName);
        Tuple tup2 = schema.makeFreshTuple(relationName);

        List<String> allColumnNames = schema.getColumnNames(relationName);
        checkArgument(!columnNames.isEmpty(), "the instance does not contain relation %s", relationName);
        BoolExpr[] agreeFormulaExprs = new BoolExpr[columnNames.size()];
        int index = 0;
        for (int i = 0; i < allColumnNames.size(); ++i) {
            if (columnNames.contains(allColumnNames.get(i))) {
                agreeFormulaExprs[index++] = context.mkEq(tup1.get(i), tup2.get(i));
            }
        }
        checkArgument(index == columnNames.size(), "some column(s) not found: %s.%s", relationName, columnNames);

        BoolExpr agreeFormula = context.mkAnd(agreeFormulaExprs);

        BoolExpr lhs = context.mkAnd(relation.apply(tup1), relation.apply(tup2), agreeFormula);
        BoolExpr rhs = tup1.tupleEqual(tup2);

        Expr[] allVars = Stream.concat(tup1.stream(), tup2.stream()).toArray(Expr[]::new);
        return context.mkForall(allVars, context.mkImplies(lhs, rhs), 1, null, null, null, null);
    }
}
