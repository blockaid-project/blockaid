package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;

import java.util.*;

public class PrimaryKeyDependency implements Dependency {
    private String relationName;
    private Set<String> columnNames;

    public PrimaryKeyDependency(String relationName, Collection<String> columnNames) {
        this.relationName = relationName;
        this.columnNames = new HashSet<String>(columnNames);
    }

    @Override
    public BoolExpr apply(Context context, Instance instance) {
        Relation relation = instance.get(this.relationName);
        Schema schema = instance.schema;
        Tuple tup1 = schema.makeFreshTuple(context, relationName);
        Tuple tup2 = schema.makeFreshTuple(context, relationName);

        List<String> allColumnNames = schema.getColumnNames(relationName);
        BoolExpr[] agreeFormulaExprs = new BoolExpr[columnNames.size()];
        int index = 0;
        for (int i = 0; i < allColumnNames.size(); ++i) {
            if (columnNames.contains(allColumnNames.get(i))) {
                agreeFormulaExprs[index++] = context.mkEq(tup1.get(i), tup2.get(i));
            }
        }
        if (index < columnNames.size()) {
            throw new RuntimeException("some column(s) not found: " + relationName + "." + columnNames);
        }

        BoolExpr agreeFormula = context.mkAnd(agreeFormulaExprs);

        List<Expr> vars = new ArrayList<>(tup1);
        vars.addAll(tup2);
        BoolExpr lhs = context.mkAnd(relation.apply(tup1.toArray(new Expr[0])), relation.apply(tup2.toArray(new Expr[0])), agreeFormula);
        BoolExpr rhs = tup1.tupleEqual(context, tup2);

        return context.mkForall(vars.toArray(new Expr[0]), context.mkImplies(lhs, rhs), 1, null, null, null, null);
    }
}
