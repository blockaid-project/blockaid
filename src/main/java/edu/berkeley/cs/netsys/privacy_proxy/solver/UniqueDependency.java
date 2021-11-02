package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.*;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.*;

public class UniqueDependency implements Dependency {
    private final String relationName;
    private final ImmutableSet<String> columnNames;
    private final ImmutableList<String> relevantColumns;

    public UniqueDependency(String relationName, Collection<String> columnNames) {
        this.relationName = checkNotNull(relationName);
        checkArgument(!columnNames.isEmpty());
        this.columnNames = ImmutableSet.copyOf(columnNames);
        this.relevantColumns = columnNames.stream()
                .map(colName -> (relationName + "." + colName).toUpperCase())
                .collect(ImmutableList.toImmutableList());
    }

    @Override
    public <C extends Z3ContextWrapper<?, ?, ?, ?>> Iterable<BoolExpr> apply(Instance<C> instance) {
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

    @Override
    public ImmutableSet<String> getFromRelations() {
        return ImmutableSet.of(relationName);
    }

    @Override
    public ImmutableSet<String> getToRelations() {
        // The right-hand side is the "empty" query, which doesn't reference any relations.
        return ImmutableSet.of();
    }

    private <C extends Z3ContextWrapper<?, ?, ?, ?>> Iterable<BoolExpr> applyGeneral(Instance<C> instance) {
        C context = instance.getContext();

        Relation<C> relation = instance.get(this.relationName);
        Schema<C> schema = instance.getSchema();
        Tuple<C> tup1 = schema.makeFreshQuantifiedTuple(relationName);
        Tuple<C> tup2 = schema.makeFreshQuantifiedTuple(relationName);

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

        List<Expr<?>> allVars = Stream.concat(tup1.stream(), tup2.stream()).collect(Collectors.toList());
        return List.of(context.myMkForall(allVars, context.mkImplies(lhs, rhs)));
    }

    private <C extends Z3ContextWrapper<?, ?, ?, ?>> Iterable<BoolExpr> applyConcrete(Instance<C> instance) {
        C context = instance.getContext();

        ConcreteRelation<C> relation = (ConcreteRelation<C>) instance.get(this.relationName);
        Schema<C> schema = instance.getSchema();

        List<String> allColumnNames = schema.getColumnNames(relationName);
        checkArgument(!columnNames.isEmpty(), "empty primary/unique key for relation %s", relationName);

        ImmutableList<Tuple<C>> tuples = relation.getTuples();
        if (tuples.isEmpty()) {
            return List.of();
        }

        ImmutableList<BoolExpr> exists = relation.getExists();
        Table<Integer, Integer, Expr<?>> syms = HashBasedTable.create(); // Maps (pk column index, tuple index) -> value at that column.
        int index = 0;
        for (int i = 0; i < allColumnNames.size(); ++i) {
            if (columnNames.contains(allColumnNames.get(i))) {
                for (int j = 0; j < tuples.size(); ++j) {
                    syms.put(index, j, tuples.get(j).get(i));
                }
                ++index;
            }
        }
        checkArgument(index == columnNames.size(), "some column(s) not found: %s.%s", relationName, columnNames);

        // Fast path: single-column integer primary key.
        // Unclear whether this is actually faster, though.
        if (columnNames.size() == 1 && syms.get(0, 0).getSort().equals(context.getCustomIntSort())) {
            return List.of(context.mkDistinctUntyped(syms.row(0).values()));
        }

        List<BoolExpr> exprs = new ArrayList<>();
        for (int i = 0; i < tuples.size(); ++i) {
            for (int j = i + 1; j < tuples.size(); ++j) {
                // (tup i exists /\ tup j exists) ==> not (tup i[pk columns] == tup j[pk columns]).
                BoolExpr[] constraint = new BoolExpr[columnNames.size() + 2];
                for (int k = 0; k < columnNames.size(); ++k) {
                    constraint[k] = context.mkEq(syms.get(k, i), syms.get(k, j));
                }
                constraint[constraint.length - 2] = exists.get(i);
                constraint[constraint.length - 1] = exists.get(j);
                exprs.add(context.mkNot(context.mkAnd(constraint)));
            }
        }

        return exprs;
    }
}
