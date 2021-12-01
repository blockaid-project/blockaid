package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.*;
import org.checkerframework.checker.nullness.qual.Nullable;

import java.math.BigDecimal;
import java.sql.Date;
import java.sql.Timestamp;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;

class CustomSorts {
    private final Z3CustomSortsContext context;
    private final boolean quantifierFree;

    // Dependent types would come in handy here...
    final UninterpretedSort intSort;
    final UninterpretedSort boolSort;
    final UninterpretedSort dateSort;
    final UninterpretedSort tsSort;
    final UninterpretedSort realSort;
    final UninterpretedSort stringSort;

    private final ImmutableMap<UninterpretedSort, Expr<UninterpretedSort>> sort2NullExpr;

    private final String sortDeclarationSMT;
    private final List<Values> valuesStack;

    private final ImmutableMap<UninterpretedSort, FuncDecl<BoolSort>> sort2LtFunc;
    private final FuncDecl<BoolSort> stringLikeFunc;

    private final ImmutableList<BoolExpr> axioms;

    private static final Function<Values, Map<Date, Expr<UninterpretedSort>>> PICK_DATE = v -> v.dateValues;
    private static final Function<Values, Map<Timestamp, Expr<UninterpretedSort>>> PICK_TS = v -> v.tsValues;
    private static final Function<Values, Map<BigDecimal, Expr<UninterpretedSort>>> PICK_INT = v -> v.intValues;
    private static final Function<Values, Map<Double, Expr<UninterpretedSort>>> PICK_REAL = v -> v.realValues;
    private static final Function<Values, Map<String, Expr<UninterpretedSort>>> PICK_STRING = v -> v.stringValues;
    private static final Function<Values, Map<Boolean, Expr<UninterpretedSort>>> PICK_BOOL = v -> v.boolValues;

    private static class Values {
        private final Map<Date, Expr<UninterpretedSort>> dateValues = new HashMap<>();
        private final Map<Timestamp, Expr<UninterpretedSort>> tsValues = new HashMap<>();
        private final Map<BigDecimal, Expr<UninterpretedSort>> intValues = new HashMap<>();
        private final Map<Double, Expr<UninterpretedSort>> realValues = new HashMap<>();
        private final Map<String, Expr<UninterpretedSort>> stringValues = new HashMap<>();
        private final Map<Boolean, Expr<UninterpretedSort>> boolValues = new HashMap<>();

        // Here we use an `IdentityHashMap` to avoid hashing Z3 expressions and save some time.
        // The keys in this map are always fresh constants and shouldn't be re-created after their initial creation.
        // Therefore, there should be only one object for each expression, and we can get away with identity comparison.
        private final IdentityHashMap<Expr<UninterpretedSort>, Object> expr2Obj = new IdentityHashMap<>();
    }

    CustomSorts(Z3CustomSortsContext context, boolean quantifierFree) {
        this.context = context;
        Context rawContext = context.rawContext;
        this.quantifierFree = quantifierFree;

        intSort = rawContext.mkUninterpretedSort("CS!INT");
        dateSort = rawContext.mkUninterpretedSort("CS!DATE");
        tsSort = rawContext.mkUninterpretedSort("CS!TS");
        boolSort = rawContext.mkUninterpretedSort("CS!BOOL");
        realSort = rawContext.mkUninterpretedSort("CS!REAL");
        stringSort = rawContext.mkUninterpretedSort("CS!STRING");
        ImmutableList<UninterpretedSort> allSorts = ImmutableList.of(intSort, dateSort, tsSort, boolSort, realSort, stringSort);

        sortDeclarationSMT = allSorts.stream()
                .map(s -> "(declare-sort " + s.getSExpr() + " 0)")
                .collect(Collectors.joining("\n"));

        valuesStack = new ArrayList<>();
        valuesStack.add(new Values());

        // We make a less-than function for every sort, even though some of them might not be comparable (?)
        sort2LtFunc = allSorts.stream().collect(ImmutableMap.toImmutableMap(
                sort -> sort, // key
                sort -> context.mkFuncDecl("lt!" + sort.getSExpr(),
                        new Sort[]{sort, sort}, context.rawContext.getBoolSort()) // value
        ));

        stringLikeFunc = context.mkFuncDecl("like", new Sort[]{stringSort, stringSort},
                context.rawContext.getBoolSort());

        if (quantifierFree) {
            axioms = ImmutableList.of(); // No axioms, which require quantifiers.
        } else {
            ImmutableList.Builder<BoolExpr> axiomsBuilder = ImmutableList.builder();

            // Transitivity axiom for less-than functions.
            for (Map.Entry<UninterpretedSort, FuncDecl<BoolSort>> entry : sort2LtFunc.entrySet()) {
                UninterpretedSort sort = entry.getKey();
                FuncDecl<BoolSort> func = entry.getValue();
                Expr<UninterpretedSort> x = rawContext.mkConst("x", sort),
                        y = rawContext.mkConst("y", sort),
                        z = rawContext.mkConst("z", sort);
                BoolExpr ltTrans = rawContext.mkForall(
                        new Expr[]{x, y, z},
                        rawContext.mkImplies(
                                rawContext.mkAnd(func.apply(x, y), func.apply(y, z)), func.apply(x, z)
                        ), 1, null, null, null, null
                );
                axiomsBuilder.add(ltTrans);
            }
            axioms = axiomsBuilder.build();
        }

        sort2NullExpr = ImmutableMap.<UninterpretedSort, Expr<UninterpretedSort>>builder()
                .put(boolSort, getBool(null))
                .put(intSort, getInt((BigDecimal) null))
                .put(dateSort, getDate(null))
                .put(tsSort, getTimestamp(null))
                .put(realSort, getReal(null))
                .put(stringSort, getString(null))
                .build();
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

    private <T> Expr<UninterpretedSort> get(@Nullable T value, UninterpretedSort sort,
                                            Function<Values, Map<T, Expr<UninterpretedSort>>> valueMapPicker) {
        for (int i = valuesStack.size(); i-- > 0; ) {
            Map<T, Expr<UninterpretedSort>> valueMap = valueMapPicker.apply(valuesStack.get(i));
            Expr<UninterpretedSort> e = valueMap.get(value);
            if (e != null) {
                return e;
            }
        }
        Expr<UninterpretedSort> c = value == null ? context.mkFreshConst(sort.getSExpr() + "!null", sort)
                : context.mkFreshConst(sort.getSExpr(), sort);
        Values vs = valuesStack.get(valuesStack.size() - 1);
        valueMapPicker.apply(vs).put(value, c);
        vs.expr2Obj.put(c, value);
        return c;
    }

    Expr<UninterpretedSort> getDate(@Nullable Date date) {
        return get(date, dateSort, PICK_DATE);
    }

    Expr<UninterpretedSort> getTimestamp(@Nullable Timestamp ts) {
        return get(ts, tsSort, PICK_TS);
    }

    Expr<UninterpretedSort> getInt(@Nullable Long value) {
        return get(value == null ? null : BigDecimal.valueOf(value), intSort, PICK_INT);
    }

    Expr<UninterpretedSort> getInt(@Nullable BigDecimal value) {
        return get(value, intSort, PICK_INT);
    }

    Expr<UninterpretedSort> getBool(@Nullable Boolean value) {
        return get(value, boolSort, PICK_BOOL);
    }

    Expr<UninterpretedSort> getReal(@Nullable Double value) {
        return get(value, realSort, PICK_REAL);
    }

    Expr<UninterpretedSort> getString(@Nullable String value) {
        return get(value, stringSort, PICK_STRING);
    }

    /**
     * Checks whether the expression corresponds to a constant value and, if so, returns the value.
     * TODO(zhangwen): The ugly return type is due to `Optional.of(null)` not being allowed.
     * @param e the expression to check.
     * @return if not a constant value, empty; otherwise, the value (potentially null) as an `Optional`.
     */
    Optional<Optional<Object>> getValueForExpr(Expr<?> e) {
        for (int i = valuesStack.size(); i-- > 0; ) {
            Values vs = valuesStack.get(i);
            if (vs.expr2Obj.containsKey(e)) {
                return Optional.of(Optional.ofNullable(vs.expr2Obj.get(e)));
            }
        }
        return Optional.empty();
    }

    private <T extends Comparable<? super T>> Collection<BoolExpr> mkLtConstraints(
            Map<T, Expr<UninterpretedSort>> exprs) {
        // Filter out the null key -- don't include it in the less-than constraints.
        List<T> keys = exprs.keySet().stream().filter(Objects::nonNull).sorted().collect(Collectors.toList());
        if (keys.size() <= 1) {
            return Collections.emptyList();
        }

        ArrayList<BoolExpr> res = new ArrayList<>();
        if (quantifierFree) {
            // In the quantifier-free case, there's no transitivity axiom imposed on our less-than predicate.
            // Therefore, add a less-than constraint for every pair of values.
            for (int i = 0; i < keys.size(); ++i) {
                Expr<UninterpretedSort> thisElem = exprs.get(keys.get(i));
                for (int j = i + 1; j < keys.size(); ++j) {
                    Expr<UninterpretedSort> otherElem = exprs.get(keys.get(j));
                    res.add(mkRawCustomLt(thisElem, otherElem));
                }
            }
        } else {
            for (int i = 0; i < keys.size() - 1; ++i) {
                Expr<UninterpretedSort> thisElem = exprs.get(keys.get(i)), nextElem = exprs.get(keys.get(i + 1));
                res.add(mkRawCustomLt(thisElem, nextElem));
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

    BoolExpr mkRawCustomLt(Expr<?> left, Expr<?> right) {
        if (!(left.getSort() instanceof UninterpretedSort leftSort)) {
            throw new IllegalArgumentException("left sort must be uninterpreted, got: " + left.getSort());
        }
        if (!(right.getSort() instanceof UninterpretedSort rightSort)) {
            throw new IllegalArgumentException("right sort must be uninterpreted, got: " + right.getSort());
        }
        checkArgument(leftSort.equals(rightSort),
                "sort of left expression " + left + " (" + leftSort +
                        ") is different from right expression " + right + " (" + rightSort  + ")"
        );
        return (BoolExpr) sort2LtFunc.get(leftSort).apply(left, right);
    }

    BoolExpr mkRawStringLike(Expr<?> left, Expr<?> right) {
        return (BoolExpr) stringLikeFunc.apply(left, right);
    }

    Expr<UninterpretedSort> mkNull(UninterpretedSort s) {
        Expr<UninterpretedSort> nullExpr = sort2NullExpr.get(s);
        if (nullExpr == null) {
            throw new IllegalArgumentException("no null value for sort: " + s);
        }
        return nullExpr;
    }
}
