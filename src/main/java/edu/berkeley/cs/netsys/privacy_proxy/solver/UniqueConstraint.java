package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.*;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.*;

public class UniqueConstraint implements Constraint {
    private final String relationName;
    private final ImmutableSet<String> columnNames;
    private final ImmutableList<String> relevantColumns;

    public UniqueConstraint(String relationName, Collection<String> columnNames) {
        this.relationName = checkNotNull(relationName);
        checkArgument(!columnNames.isEmpty());
        this.columnNames = ImmutableSet.copyOf(columnNames);
        this.relevantColumns = columnNames.stream()
                .map(colName -> (relationName + "." + colName).toUpperCase())
                .collect(ImmutableList.toImmutableList());
    }

    @Override
    public Iterable<BoolExpr> apply(Instance instance) {
        if (instance.isConcrete) {
            return applyConcrete(instance);
        } else {
            return applyGeneral(instance);
        }
    }

    @Override
    public List<String> getRelevantColumns() {
        return relevantColumns;
    }

    private Iterable<BoolExpr> applyGeneral(Instance instance) {
        Z3ContextWrapper context = instance.getContext();

        Relation relation = instance.get(this.relationName);
        Schema schema = instance.schema;
        Tuple tup1 = schema.makeFreshQuantifiedTuple(relationName);
        Tuple tup2 = schema.makeFreshQuantifiedTuple(relationName);

        List<String> allColumnNames = schema.getColumnNames(relationName);
        checkArgument(!columnNames.isEmpty(), "empty primary/unique key for relation %s", relationName);
        BoolExpr[] agreeFormulaExprs = new BoolExpr[columnNames.size()];
        int index = 0;
        for (int i = 0; i < allColumnNames.size(); ++i) {
            if (columnNames.contains(allColumnNames.get(i))) {
                agreeFormulaExprs[index++] = context.mkEq(tup1.get(i), tup2.get(i));
            }
        }
        checkArgument(index == columnNames.size(), "some column(s) not found: %s.%s", relationName, columnNames);

        BoolExpr agreeFormula = context.mkAnd(agreeFormulaExprs);

        BoolExpr lhs = context.mkAnd(context.mkAnd(relation.doesContainExpr(tup1)),
                context.mkAnd(relation.doesContainExpr(tup2)), agreeFormula);
        BoolExpr rhs = tup1.equalsExpr(tup2);

        Expr[] allVars = Stream.concat(tup1.stream(), tup2.stream()).toArray(Expr[]::new);
        return List.of(context.myMkForall(allVars, context.mkImplies(lhs, rhs)));
    }

    private Iterable<BoolExpr> applyConcrete(Instance instance) {
        Z3ContextWrapper context = instance.getContext();

        ConcreteRelation relation = (ConcreteRelation) instance.get(this.relationName);
        Schema schema = instance.schema;

        List<String> allColumnNames = schema.getColumnNames(relationName);
        checkArgument(!columnNames.isEmpty(), "empty primary/unique key for relation %s", relationName);

        Tuple[] tuples = relation.getTuples();
        if (tuples.length == 0) {
            return List.of();
        }

        BoolExpr[] exists = relation.getExists();
        Expr[][] syms = new Expr[columnNames.size()][]; // Maps (pk column index, tuple index) -> value at that column.
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
        checkArgument(index == columnNames.size(), "some column(s) not found: %s.%s", relationName, columnNames);

        // Fast path: single-column integer primary key.
        // Unclear whether tthis is actually faster, though.
        if (columnNames.size() == 1 && syms[0][0].getSort().equals(context.getCustomIntSort())) {
            return List.of(context.mkDistinct(syms[0]));
        }

        List<BoolExpr> exprs = new ArrayList<>();
        for (int i = 0; i < tuples.length; ++i) {
            for (int j = i + 1; j < tuples.length; ++j) {
                // (tup i exists /\ tup j exists) ==> not (tup i[pk columns] == tup j[pk columns]).
                BoolExpr[] constraint = new BoolExpr[syms.length + 2];
                for (int k = 0; k < syms.length; ++k) {
                    constraint[k] = context.mkEq(syms[k][i], syms[k][j]);
                }
                constraint[constraint.length - 2] = exists[i];
                constraint[constraint.length - 1] = exists[j];
                exprs.add(context.mkNot(context.mkAnd(constraint)));
            }
        }

        return exprs;
    }
}
