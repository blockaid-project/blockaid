package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.*;

import java.sql.Date;
import java.sql.Timestamp;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

class CustomSorts {
    private final Z3CustomSortsContext context;
    private final QuantifierOption quantifierOption;

    // Dependent types would come in handy here...
    final UninterpretedSort intSort;
    final UninterpretedSort boolSort;
    final UninterpretedSort dateSort;
    final UninterpretedSort tsSort;
    final UninterpretedSort realSort;
    final UninterpretedSort stringSort;

    private final String sortDeclarationSMT;
    private final List<Values> valuesStack;

    final FuncDecl<BoolSort> intLt;

    final ImmutableList<BoolExpr> axioms;

    private static final Function<Values, Map<Date, Expr<UninterpretedSort>>> PICK_DATE = v -> v.dateValues;
    private static final Function<Values, Map<Timestamp, Expr<UninterpretedSort>>> PICK_TS = v -> v.tsValues;
    private static final Function<Values, Map<Long, Expr<UninterpretedSort>>> PICK_INT = v -> v.intValues;
    private static final Function<Values, Map<Double, Expr<UninterpretedSort>>> PICK_REAL = v -> v.realValues;
    private static final Function<Values, Map<String, Expr<UninterpretedSort>>> PICK_STRING = v -> v.stringValues;
    private static final Function<Values, Map<Boolean, Expr<UninterpretedSort>>> PICK_BOOL = v -> v.boolValues;

    private static class Values {
        private final Map<Date, Expr<UninterpretedSort>> dateValues = new HashMap<>();
        private final Map<Timestamp, Expr<UninterpretedSort>> tsValues = new HashMap<>();
        private final Map<Long, Expr<UninterpretedSort>> intValues = new HashMap<>();
        private final Map<Double, Expr<UninterpretedSort>> realValues = new HashMap<>();
        private final Map<String, Expr<UninterpretedSort>> stringValues = new HashMap<>();
        private final Map<Boolean, Expr<UninterpretedSort>> boolValues = new HashMap<>();

        private final Map<Expr<UninterpretedSort>, Object> expr2Obj = new HashMap<>();
    }

    CustomSorts(Z3CustomSortsContext context, QuantifierOption qo) {
        this.context = context;
        this.quantifierOption = qo;
        Context rawContext = context.rawContext;

        // Int, date, and timestamp share the same sort and less-than predicate.
        intSort = dateSort = tsSort = rawContext.mkUninterpretedSort("CS!INT");
        boolSort = rawContext.mkUninterpretedSort("CS!BOOL");
        realSort = rawContext.mkUninterpretedSort("CS!REAL");
        stringSort = rawContext.mkUninterpretedSort("CS!STRING");

        // dateSort and tsSort are currently the same sort, so we don't declare them.
        this.sortDeclarationSMT = "(declare-sort " + realSort.getSExpr() + " 0)\n" +
                "(declare-sort " + boolSort.getSExpr() + " 0)\n" +
                "(declare-sort " + stringSort.getSExpr() + " 0)\n" +
                "(declare-sort " + intSort.getSExpr() + " 0)\n";

        valuesStack = new ArrayList<>();
        valuesStack.add(new Values());

        intLt = context.mkFuncDecl("lt", new Sort[]{intSort, intSort}, context.rawContext.getBoolSort());
        axioms = switch (quantifierOption) {
            case QUANTIFIER_FREE -> ImmutableList.of(); // No axioms, which require quantifiers.
            case USE_QUANTIFIERS -> {
                ImmutableList.Builder<BoolExpr> axiomsBuilder = ImmutableList.builder();

                // Integer less-than transitivity.
                Expr<UninterpretedSort> x = rawContext.mkConst("x", intSort),
                        y = rawContext.mkConst("y", intSort),
                        z = rawContext.mkConst("z", intSort);
                BoolExpr intLtTrans = rawContext.mkForall(
                        new Expr[]{x, y, z},
                        rawContext.mkImplies(
                                rawContext.mkAnd(intLt.apply(x, y), intLt.apply(y, z)), intLt.apply(x, z)
                        ), 1, null, null, null, null
                );
                axiomsBuilder.add(intLtTrans);
                yield axiomsBuilder.build();
            }
        };
    }

    void push() {
        valuesStack.add(new Values());
    }

    void pop() {
        valuesStack.remove(valuesStack.size() - 1);
    }

    private <T> Map<T, Expr<UninterpretedSort>> getAll(Function<Values, Map<T, Expr<UninterpretedSort>>> valueMapPicker)
    {
        return valuesStack.stream().map(valueMapPicker).flatMap(m -> m.entrySet().stream())
                .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
    }

    private <T> Expr<UninterpretedSort> get(T value, UninterpretedSort sort,
                                            Function<Values, Map<T, Expr<UninterpretedSort>>> valueMapPicker) {
        for (int i = valuesStack.size(); i-- > 0; ) {
            Map<T, Expr<UninterpretedSort>> valueMap = valueMapPicker.apply(valuesStack.get(i));
            Expr<UninterpretedSort> e = valueMap.get(value);
            if (e != null) {
                return e;
            }
        }
        Expr<UninterpretedSort> c = context.mkFreshConst(sort.getSExpr(), sort);
        Values vs = valuesStack.get(valuesStack.size() - 1);
        valueMapPicker.apply(vs).put(value, c);
        vs.expr2Obj.put(c, value);
        return c;
    }

    Expr<UninterpretedSort> getDate(Date date) {
        return get(date, dateSort, PICK_DATE);
    }

    Expr<UninterpretedSort> getTimestamp(Timestamp ts) {
        return get(ts, tsSort, PICK_TS);
    }

    Expr<UninterpretedSort> getInt(long value) {
        return get(value, intSort, PICK_INT);
    }

    Expr<UninterpretedSort> getBool(boolean value) {
        return get(value, boolSort, PICK_BOOL);
    }

    Expr<UninterpretedSort> getReal(double value) {
        return get(value, realSort, PICK_REAL);
    }

    Expr<UninterpretedSort> getString(String value) {
        return get(value, stringSort, PICK_STRING);
    }

    Optional<Object> getValueForExpr(Expr<?> e) {
        for (int i = valuesStack.size(); i-- > 0; ) {
            Values vs = valuesStack.get(i);
            if (vs.expr2Obj.containsKey(e)) {
                return Optional.of(vs.expr2Obj.get(e));
            }
        }
        return Optional.empty();
    }

    private <T extends Comparable<? super T>> Collection<BoolExpr> mkLtConstraints(
            Map<T, Expr<UninterpretedSort>> exprs) {
        if (exprs.size() <= 1) {
            return Collections.emptyList();
        }

        ArrayList<T> keys = new ArrayList<>(exprs.keySet());
        Collections.sort(keys);
        ArrayList<BoolExpr> res = new ArrayList<>();
        switch (quantifierOption) {
            case QUANTIFIER_FREE -> {
                // In the quantifier-free case, there's no transitivity axiom imposed on our less-than predicate.
                // Therefore, add a less-than constraint for every pair of values.
                for (int i = 0; i < keys.size(); ++i) {
                    Expr<UninterpretedSort> thisElem = exprs.get(keys.get(i));
                    for (int j = i + 1; j < keys.size(); ++j) {
                        Expr<UninterpretedSort> otherElem = exprs.get(keys.get(j));
                        res.add((BoolExpr) intLt.apply(thisElem, otherElem));
                    }
                }
            }
            case USE_QUANTIFIERS -> {
                for (int i = 0; i < keys.size() - 1; ++i) {
                    Expr<UninterpretedSort> thisElem = exprs.get(keys.get(i)), nextElem = exprs.get(keys.get(i + 1));
                    res.add((BoolExpr) intLt.apply(thisElem, nextElem));
                }
            }
        }
        return res;
    }

    private <T> void prepareSolverForSort(Solver solver, Map<T, Expr<UninterpretedSort>> m) {
        solver.add(context.mkDistinct(m.values()));
    }

    private <T> void prepareSolverForSort(Solver solver,
                                          Function<Values, Map<T, Expr<UninterpretedSort>>> valueMapPicker) {
        solver.add(context.mkDistinct(getAll(valueMapPicker).values()));
    }

    private <T extends Comparable<? super T>> void prepareSolverForComparableSort(
            Solver solver, Function<Values, Map<T, Expr<UninterpretedSort>>> valueMapPicker) {
        Map<T, Expr<UninterpretedSort>> values = getAll(valueMapPicker);
        prepareSolverForSort(solver, values);
        solver.add(mkLtConstraints(values).toArray(new BoolExpr[0]));
    }

    // Prepares Solver for use with custom sorts (adds uniqueness constraints)
    Solver prepareSolver(Solver solver) {
        prepareSolverForComparableSort(solver, PICK_DATE);
        prepareSolverForComparableSort(solver, PICK_TS);
        prepareSolverForComparableSort(solver, PICK_INT);
        prepareSolverForSort(solver, PICK_REAL);
        prepareSolverForSort(solver, PICK_STRING);
        prepareSolverForSort(solver, PICK_BOOL);
        solver.add(axioms.toArray(new BoolExpr[0]));
        return solver;
    }

    String prepareSortDeclaration() {
        // Reusing prepareSolver is messy - some constants and sorts may not be used/declared.
        return sortDeclarationSMT;
    }

    String prepareCustomValueConstraints() {
        // Reusing prepareSolver is messy - some constants and sorts may not be used/declared.
        StringBuilder sb = new StringBuilder();
        prepareSortValuesComparable(sb, PICK_DATE);
        prepareSortValuesComparable(sb, PICK_TS);
        prepareSortValuesComparable(sb, PICK_INT);
        prepareSortValues(sb, PICK_REAL);
        prepareSortValues(sb, PICK_STRING);
        prepareSortValues(sb, PICK_BOOL);
        for (BoolExpr axiom : axioms) {
            sb.append("(assert ").append(axiom.getSExpr()).append(")\n");
        }
        return sb.toString();
    }

    private <T> void prepareSortValues(StringBuilder sb,
                                       Function<Values, Map<T, Expr<UninterpretedSort>>> valueMapPicker) {
        StringBuilder distinct = new StringBuilder("(assert (distinct");
        int numValues = 0;

        for (Values vs : valuesStack) {
            for (Map.Entry<T, Expr<UninterpretedSort>> entry : valueMapPicker.apply(vs).entrySet()) {
                Expr<UninterpretedSort> expr = entry.getValue();
                distinct.append(' ').append(expr.getSExpr());
                ++numValues;
            }
        }

        distinct.append("))\n");
        if (numValues > 1) {
            sb.append(distinct).append("\n");
        }
    }

    private <T extends Comparable<? super T>> void prepareSortValuesComparable(
            StringBuilder sb, Function<Values, Map<T, Expr<UninterpretedSort>>> valueMapPicker) {
        prepareSortValues(sb, valueMapPicker);
        Map<T, Expr<UninterpretedSort>> value2Expr = getAll(valueMapPicker);
        for (BoolExpr e : mkLtConstraints(value2Expr)) {
            sb.append("(assert ").append(e.getSExpr()).append(")\n");
        }
    }
}
