package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.*;

import java.sql.Date;
import java.sql.Timestamp;
import java.util.ArrayList;
import java.util.HashMap;

import static com.google.common.base.Preconditions.checkArgument;

/**
 * Uses integer and bool sorts.  Doesn't track constants.
 */
class Z3TheoryContext<NullableInt, NullableBool> extends Z3ContextWrapper<IntSort, IntSort, IntSort, BoolSort> {
    // We represent strings using int expressions, so track the mapping.
    private final ArrayList<HashMap<String, IntNum>> strToIntNum;

    private final DatatypeSort<NullableInt> nullableIntSort;
    private final DatatypeSort<NullableBool> nullableBoolSort;

    private record NullableSortInfo<R>(DatatypeSort<R> sort, Constructor<R> nullCon, Constructor<R> valueCon,
                                       Expr<DatatypeSort<R>> nullExpr) {
        public NullableSortInfo(DatatypeSort<R> sort, Constructor<R> nullCon, Constructor<R> valueCon) {
            this(sort, nullCon, valueCon, nullCon.ConstructorDecl().apply());
        }
    }

    private final ImmutableMap<Sort, NullableSortInfo<?>> nullableSorts;

    Z3TheoryContext() {
        strToIntNum = new ArrayList<>();
        strToIntNum.add(new HashMap<>());

        Constructor<NullableInt> intNullCon = rawContext.mkConstructor("null", "is_null", null, null, null);
        Constructor<NullableInt> intValueCon = rawContext.mkConstructor("cons", "is_cons", new String[]{"v"},
                new Sort[]{rawContext.getIntSort()}, null);
        {
            @SuppressWarnings("unchecked")
            Constructor<NullableInt>[] constructors = new Constructor[]{intNullCon, intValueCon};
            nullableIntSort = rawContext.mkDatatypeSort("nullableInt", constructors);
        }

        Constructor<NullableBool> boolNullCon = rawContext.mkConstructor("null", "is_null", null, null, null);
        Constructor<NullableBool> boolValueCon = rawContext.mkConstructor("cons", "is_cons", new String[]{"v"},
                new Sort[]{rawContext.getBoolSort()}, null);
        {
            @SuppressWarnings("unchecked") Constructor<NullableBool>[] constructors = new Constructor[]{boolNullCon, boolValueCon};
            nullableBoolSort = rawContext.mkDatatypeSort("nullableBool", constructors);
        }

        nullableSorts = ImmutableMap.of(
                nullableIntSort, new NullableSortInfo<>(nullableIntSort, intNullCon, intValueCon),
                nullableBoolSort, new NullableSortInfo<>(nullableBoolSort, boolNullCon, boolValueCon)
        );
    }

    @Override
    public boolean areDistinctConstants(Expr<?> lhs, Expr<?> rhs) {
        if (!(lhs instanceof IntNum lhsNum) || !(rhs instanceof IntNum rhsNum)) {
            return false;
        }
        return lhsNum.getInt64() != rhsNum.getInt64();
    }

    @Override
    public BoolExpr mkBoolConst(String s) {
        return rawContext.mkBoolConst(s);
    }

    @Override
    public <S extends Sort> Expr<S> mkConst(String s, S sort) {
        return rawContext.mkConst(s, sort);
    }

    @Override
    public <S extends Sort> Expr<S> mkFreshConst(String s, S sort) {
        return rawContext.mkFreshConst(s, sort);
    }

    // Not tracked.
    @Override
    public <S extends Sort> Expr<S> mkFreshQuantifiedConst(String s, S sort) {
        return rawContext.mkFreshConst(s, sort);
    }

    @Override
    public void pushTrackConsts() {
        strToIntNum.add(new HashMap<>());
    }

    @Override
    public void popTrackConsts() {
        strToIntNum.remove(strToIntNum.size() - 1);
    }

    @Override
    public TrackedDecls getAllTrackedDecls() {
        return EmptyTrackedDecls.getSingleton();
    }

    @Override
    public String prepareSortDeclaration() {
        return "";
    }

    @Override
    public String prepareCustomValueConstraints() {
        return "";
    }

    @Override
    public Solver mkSolver() {
        return rawContext.mkSolver();
    }

    @Override
    public Solver mkSolver(Symbol symbol) {
        return rawContext.mkSolver(symbol);
    }

    @Override
    public Solver mkQfSolver() {
        // FIXME(zhangwen): Specify a theory?
        return mkSolver();
    }

    @Override
    public IntSort getDateSort() {
        return rawContext.getIntSort();
    }

    @Override
    public Expr<IntSort> mkDate(Date date) {
        return rawContext.mkInt(date.getTime());
    }

    @Override
    public IntSort getTimestampSort() {
        return rawContext.getIntSort();
    }

    @Override
    public Sort getNullableCustomIntSort() {
        return nullableIntSort;
    }

    @Override
    public Sort getNullableCustomBoolSort() {
        return nullableBoolSort;
    }

    @Override
    public Sort getNullableCustomRealSort() {
        return nullableIntSort;
    }

    @Override
    public Sort getNullableCustomStringSort() {
        return nullableIntSort;
    }

    @Override
    public Sort getNullableDateSort() {
        return nullableIntSort;
    }

    @Override
    public Sort getNullableTimestampSort() {
        return nullableIntSort;
    }

    @Override
    public Expr<IntSort> mkTimestamp(Timestamp ts) {
        return rawContext.mkInt(
                // Number of nanoseconds since epoch.
                ts.getTime() * 1000000 + ts.getNanos() % 1000000
        );
    }

    @Override
    public BoolExpr mkSqlIsNull(Expr<?> e) {
        NullableSortInfo<?> info = nullableSorts.get(e.getSort());
        if (info == null) { // Not a nullable type, thus cannot be null.
            return rawContext.mkFalse();
        }
        return (BoolExpr) info.nullCon().getTesterDecl().apply(e);
    }

    @Override
    public BoolExpr mkSqlIsNotNull(Expr<?> e) {
        NullableSortInfo<?> info = nullableSorts.get(e.getSort());
        if (info == null) { // Not a nullable type, thus must be non-null.
            return rawContext.mkTrue();
        }
        return (BoolExpr) info.valueCon().getTesterDecl().apply(e);
    }

    @Override
    protected boolean isSortNullable(Sort s) {
        return nullableSorts.containsKey(s);
    }

    @Override
    protected Expr<?> getValueFromMaybeNullable(Expr<?> e) {
        NullableSortInfo<?> info = nullableSorts.get(e.getSort());
        if (info == null) { // Not a nullable sort.
            return e;
        }
        return info.valueCon().getAccessorDecls()[0].apply(e);
    }

    @Override
    public <S extends Sort> Expr<S> mkNull(S sort) {
        NullableSortInfo<?> info = nullableSorts.get(sort);
        checkArgument(info != null, "sort " + sort + " is not nullable");
        @SuppressWarnings("unchecked") Expr<S> nullExpr = (Expr<S>) info.nullExpr();
        return nullExpr;
    }

    @Override
    public IntSort getCustomIntSort() {
        return rawContext.getIntSort();
    }

    @Override
    public Expr<IntSort> mkCustomInt(long value) {
        return rawContext.mkInt(value);
    }

    @Override
    public BoolExpr mkRawCustomIntLt(Expr<?> left, Expr<?> right) {
        return rawContext.mkLt((IntExpr) left, (IntExpr) right);
    }

    @Override
    public IntSort getCustomRealSort() {
        return rawContext.getIntSort();
    }

    @Override
    public Expr<IntSort> mkCustomReal(double value) {
        return rawContext.mkInt(Double.doubleToRawLongBits(value));
    }

    @Override
    public IntSort getCustomStringSort() {
        return rawContext.getIntSort();
    }

    @Override
    public BoolSort getCustomBoolSort() {
        return rawContext.getBoolSort();
    }

    @Override
    public Expr<IntSort> mkCustomString(String value) {
        int numStringsSoFar = 0;
        // Has this string been assigned an `IntNum` before?
        for (HashMap<String, IntNum> m : strToIntNum) {
            IntNum res = m.get(value);
            if (res != null) {
                return res;
            }
            numStringsSoFar += m.size();
        }

        // Assign a new `IntNum` to it.
        IntNum res = rawContext.mkInt(numStringsSoFar);
        HashMap<String, IntNum> lastMap = strToIntNum.get(strToIntNum.size() - 1);
        lastMap.put(value, res);
        return res;
    }

    @Override
    public BoolExpr mkCustomBool(boolean value) {
        return rawContext.mkBool(value);
    }

    @Override
    public <R extends Sort> FuncDecl<R> mkFuncDecl(String s, Sort[] sorts, R sort) {
        return rawContext.mkFuncDecl(s, sorts, sort);
    }

    @Override
    public <R extends Sort> FuncDecl<R> mkFreshFuncDecl(String s, Sort[] sorts, R sort) {
        return rawContext.mkFreshFuncDecl(s, sorts, sort);
    }
}
