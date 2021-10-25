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

    final Sort dateSort;
    final Sort tsSort;
    final Sort intSort;
    final Sort realSort;
    final Sort stringSort;
    final Sort boolSort;

    private final String sortDeclarationSMT;
    private final List<Values> valuesStack;

    final FuncDecl intLt;
    final ImmutableList<BoolExpr> intLtAxioms;

    private static final Function<Values, Map<Date, Expr>> PICK_DATE = v -> v.dateValues;
    private static final Function<Values, Map<Timestamp, Expr>> PICK_TS = v -> v.tsValues;
    private static final Function<Values, Map<Long, Expr>> PICK_INT = v -> v.intValues;
    private static final Function<Values, Map<Double, Expr>> PICK_REAL = v -> v.realValues;
    private static final Function<Values, Map<String, Expr>> PICK_STRING = v -> v.stringValues;
    private static final Function<Values, Map<Boolean, Expr>> PICK_BOOL = v -> v.boolValues;

    private static class Values {
        private final Map<Date, Expr> dateValues = new HashMap<>();
        private final Map<Timestamp, Expr> tsValues = new HashMap<>();
        private final Map<Long, Expr> intValues = new HashMap<>();
        private final Map<Double, Expr> realValues = new HashMap<>();
        private final Map<String, Expr> stringValues = new HashMap<>();
        private final Map<Boolean, Expr> boolValues = new HashMap<>();

        private final Map<Expr, Object> expr2Obj = new HashMap<>();
    }

    CustomSorts(Z3CustomSortsContext context, QuantifierOption qo) {
        this.context = context;
        this.quantifierOption = qo;
        Context rawContext = context.rawContext;

        intSort = rawContext.mkUninterpretedSort("CS!INT");
//            dateSort = context.mkUninterpretedSort("CS!DATE");
//            tsSort = context.mkUninterpretedSort("CS!TS");
        dateSort = intSort;
        tsSort = intSort;
        realSort = rawContext.mkUninterpretedSort("CS!REAL");
        stringSort = rawContext.mkUninterpretedSort("CS!STRING");
        boolSort = rawContext.mkUninterpretedSort("CS!BOOL");

        // dateSort and tsSort are currently the same sort, so we don't declare them.
        this.sortDeclarationSMT = "(declare-sort " + realSort.getSExpr() + " 0)\n" +
                "(declare-sort " + stringSort.getSExpr() + " 0)\n" +
                "(declare-sort " + intSort.getSExpr() + " 0)\n" +
                "(declare-sort " + boolSort.getSExpr() + " 0)\n";

        valuesStack = new ArrayList<>();
        valuesStack.add(new Values());

        intLt = context.mkFuncDecl("lt", new Sort[]{intSort, intSort}, context.rawContext.getBoolSort());
        intLtAxioms = switch (quantifierOption) {
            case QUANTIFIER_FREE -> ImmutableList.of(); // No axioms, which require quantifiers.
            case USE_QUANTIFIERS -> {
                Expr x = rawContext.mkConst("x", intSort), y = rawContext.mkConst("y", intSort),
                        z = rawContext.mkConst("z", intSort);
                BoolExpr trans = rawContext.mkForall(
                        new Expr[]{x, y, z},
                        rawContext.mkImplies(
                                rawContext.mkAnd((BoolExpr) intLt.apply(x, y), (BoolExpr) intLt.apply(y, z)),
                                (BoolExpr) intLt.apply(x, z)
                        ), 1, null, null, null, null
                );
                yield ImmutableList.of(trans);
            }
        };
    }

    void push() {
        valuesStack.add(new Values());
    }

    void pop() {
        valuesStack.remove(valuesStack.size() - 1);
    }

    <T> Map<T, Expr> getAll(Function<Values, Map<T, Expr>> valueMapPicker)
    {
        return valuesStack.stream().map(valueMapPicker).flatMap(m -> m.entrySet().stream())
                .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
    }

    private <T> Expr get(T value, Sort sort, Function<Values, Map<T, Expr>> valueMapPicker) {
        for (int i = valuesStack.size(); i-- > 0; ) {
            Map<T, Expr> valueMap = valueMapPicker.apply(valuesStack.get(i));
            Expr e = valueMap.get(value);
            if (e != null) {
                return e;
            }
        }
        Expr c = context.mkFreshConst(sort.getSExpr(), sort);
        Values vs = valuesStack.get(valuesStack.size() - 1);
        valueMapPicker.apply(vs).put(value, c);
        vs.expr2Obj.put(c, value);
        return c;
    }

    Expr getDate(Date date) {
        return get(date, dateSort, PICK_DATE);
    }

    Expr getTimestamp(Timestamp ts) {
        return get(ts, tsSort, PICK_TS);
    }

    Expr getInt(long value) {
        return get(value, intSort, PICK_INT);
    }

    Expr getReal(double value) {
        return get(value, realSort, PICK_REAL);
    }

    Expr getString(String value) {
        return get(value, stringSort, PICK_STRING);
    }

    Expr getBool(boolean value) {
        return get(value, boolSort, PICK_BOOL);
    }

    Optional<Object> getValueForExpr(Expr e) {
        for (int i = valuesStack.size(); i-- > 0; ) {
            Values vs = valuesStack.get(i);
            if (vs.expr2Obj.containsKey(e)) {
                return Optional.of(vs.expr2Obj.get(e));
            }
        }
        return Optional.empty();
    }

    private <T extends Comparable<? super T>> Collection<BoolExpr> mkLtConstraints(Map<T, Expr> exprs) {
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
                    Expr thisElem = exprs.get(keys.get(i));
                    for (int j = i + 1; j < keys.size(); ++j) {
                        Expr otherElem = exprs.get(keys.get(j));
                        res.add((BoolExpr) intLt.apply(thisElem, otherElem));
                    }
                }
            }
            case USE_QUANTIFIERS -> {
                for (int i = 0; i < keys.size() - 1; ++i) {
                    Expr thisElem = exprs.get(keys.get(i)), nextElem = exprs.get(keys.get(i + 1));
                    res.add((BoolExpr) intLt.apply(thisElem, nextElem));
                }
            }
        }
        return res;
    }

    private <T> void prepareSolverForSort(Solver solver, Map<T, Expr> m) {
        solver.add(context.mkDistinct(m.values()));
    }

    private <T> void prepareSolverForSort(Solver solver, Function<Values, Map<T, Expr>> valueMapPicker) {
        solver.add(context.mkDistinct(getAll(valueMapPicker).values()));
    }

    private <T extends Comparable<? super T>> void prepareSolverForComparableSort(
            Solver solver, Function<Values, Map<T, Expr>> valueMapPicker) {
        Map<T, Expr> values = getAll(valueMapPicker);
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
        solver.add(intLtAxioms.toArray(new BoolExpr[0]));
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
        for (BoolExpr axiom : intLtAxioms) {
            sb.append("(assert ").append(axiom.getSExpr()).append(")\n");
        }
        return sb.toString();
    }

    private <T> void prepareSortValues(StringBuilder sb, Function<Values, Map<T, Expr>> valueMapPicker) {
        StringBuilder distinct = new StringBuilder("(assert (distinct");
        int numValues = 0;

        for (Values vs : valuesStack) {
            for (Map.Entry<T, Expr> entry : valueMapPicker.apply(vs).entrySet()) {
                Expr expr = entry.getValue();
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
            StringBuilder sb, Function<Values, Map<T, Expr>> valueMapPicker) {
        prepareSortValues(sb, valueMapPicker);
        Map<T, Expr> value2Expr = getAll(valueMapPicker);
        for (BoolExpr e : mkLtConstraints(value2Expr)) {
            sb.append("(assert ").append(e.getSExpr()).append(")\n");
        }
    }
}
