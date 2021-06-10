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
        if (instance.isConcrete) {
            return applyConcrete(instance);
        } else {
            return applyGeneral(instance);
        }
    }

    private BoolExpr applyGeneral(Instance instance) {
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

    private BoolExpr applyConcrete(Instance instance) {
        Context context = instance.getContext();

        ConcreteRelation relation = (ConcreteRelation) instance.get(this.relationName);
        Schema schema = instance.schema;

        List<String> allColumnNames = schema.getColumnNames(relationName);
        checkArgument(!columnNames.isEmpty(), "the instance does not contain relation %s", relationName);

        Tuple[] tuples = relation.getTuples();
        BoolExpr[] exists = relation.getExists();
        Expr[][] syms = new Expr[columnNames.size()][];
        int index = 0;
        for (int i = 0; i < allColumnNames.size(); ++i) {
            if (columnNames.contains(allColumnNames.get(i))) {
                syms[index] = new Expr[tuples.length];
                for (int j = 0; j < tuples.length; ++j) {
                    syms[index][j] = tuples[j].get(i);
                }
                ++index;
            }
        }

        List<BoolExpr> exprs = new ArrayList<>();
        for (int i = 0; i < tuples.length; ++i) {
            for (int j = i + 1; j < tuples.length; ++j) {
                BoolExpr[] constraint = new BoolExpr[syms.length + 2];
                for (int k = 0; k < syms.length; ++k) {
                    constraint[k] = context.mkEq(syms[k][i], syms[k][j]);
                }
                constraint[constraint.length - 2] = exists[i];
                constraint[constraint.length - 1] = exists[j];
                exprs.add(context.mkNot(context.mkAnd(constraint)));
            }
        }

        return context.mkAnd(exprs.toArray(new BoolExpr[0]));
    }
}
