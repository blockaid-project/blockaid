package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.google.common.cache.*;
import com.microsoft.z3.*;

import java.math.BigDecimal;
import java.sql.Date;
import java.sql.Timestamp;
import java.util.*;

/**
 * Custom Z3 Context to track constants and use uninterpreted sorts for everything.
 * Assumes that mkSolver is only called after the formula is generated (otherwise,
 * some values may be missing).
 */
public class Z3CustomSortsContext extends Z3ContextWrapper<UninterpretedSort, UninterpretedSort, UninterpretedSort, UninterpretedSort> {
    private final ArrayList<BaseTrackedDecls> trackedDeclStack;
    private final CustomSorts customSorts;
    private final boolean doSimplify;

    private record ExprPair(Expr<?> lhs, Expr<?> rhs) {}
    // Cache for formula for SMT equality.
    private final LoadingCache<ExprPair, BoolExpr> rawEqCache;

    Z3CustomSortsContext(Set<ContextOption> options) {
        this.trackedDeclStack = new ArrayList<>();
        trackedDeclStack.add(new BaseTrackedDecls());

        boolean quantifierFree = options.contains(ContextOption.QUANTIFIER_FREE);
        this.customSorts = new CustomSorts(this, quantifierFree);

        this.doSimplify = options.contains(ContextOption.DO_SIMPLIFY);

        this.rawEqCache = CacheBuilder.newBuilder().maximumSize(10000).build(
                new CacheLoader<>() {
                    @Override
                    public BoolExpr load(ExprPair exprPair) {
                        return rawContext.mkEq(exprPair.lhs, exprPair.rhs);
                    }
                }
        );
    }

    @Override
    public boolean areDistinctConstants(Expr<?> lhs, Expr<?> rhs) {
        Optional<Optional<Object>> lhsV = customSorts.getValueForExpr(lhs), rhsV = customSorts.getValueForExpr(rhs);
        return lhsV.isPresent() && rhsV.isPresent() && !lhsV.get().equals(rhsV.get());
    }

    private <S extends Sort, T extends Expr<S>> T trackConst(T c) {
        for (BaseTrackedDecls decls : trackedDeclStack) {
            if (decls.containsConst(c)) {
                return c;
            }
        }
        trackedDeclStack.get(trackedDeclStack.size() - 1).addConst(c);
        return c;
    }

    private <R extends Sort> FuncDecl<R> trackFuncDecl(FuncDecl<R> f) {
        for (BaseTrackedDecls decls : trackedDeclStack) {
            if (decls.containsFuncDecl(f)) {
                return f;
            }
        }
        trackedDeclStack.get(trackedDeclStack.size() - 1).addFuncDecl(f);
        return f;
    }

    @Override
    public BoolExpr mkBoolConst(String s) {
        return trackConst(rawContext.mkBoolConst(s));
    }

    @Override
    public <S extends Sort> Expr<S> mkConst(String s, S sort) {
        return trackConst(rawContext.mkConst(s, sort));
    }

    @Override
    public <S extends Sort> Expr<S> mkFreshConst(String s, S sort) {
        return trackConst(rawContext.mkFreshConst(s, sort));
    }

    // Not tracked.
    @Override
    public <S extends Sort> Expr<S> mkFreshQuantifiedConst(String s, S sort) {
        return rawContext.mkFreshConst(s, sort);
    }

    @Override
    public void pushTrackConsts() {
        customSorts.push();
        trackedDeclStack.add(new BaseTrackedDecls());
    }

    @Override
    public void popTrackConsts() {
        trackedDeclStack.remove(trackedDeclStack.size() - 1);
        customSorts.pop();
    }

    // DO NOT track any new consts / func decls while iterating through the returned iterables!
    @Override
    public TrackedDecls getAllTrackedDecls() {
        return new MergedTrackedDecls(trackedDeclStack);
    }

    @Override
    public String prepareSortDeclaration() {
        return customSorts.prepareSortDeclaration();
    }

    @Override
    public String prepareCustomValueConstraints() {
        return customSorts.prepareCustomValueConstraints();
    }

    @Override
    public Solver mkSolver() {
        return customSorts.prepareSolver(rawContext.mkSolver());
    }

    @Override
    public Solver mkSolver(Symbol symbol) {
        return customSorts.prepareSolver(rawContext.mkSolver(symbol));
    }

    @Override
    public Solver mkQfSolver() {
        return mkSolver(rawContext.mkSymbol("QF_UF"));
    }

    @Override
    public UninterpretedSort getDateSort() {
        return customSorts.dateSort;
    }

    @Override
    public Expr<UninterpretedSort> mkDate(Date date) {
        return trackConst(customSorts.getDate(date));
    }

    @Override
    public UninterpretedSort getTimestampSort() {
        return customSorts.tsSort;
    }

    @Override
    public Sort getNullableCustomIntSort() {
        return getCustomIntSort();
    }

    @Override
    public Sort getNullableCustomBoolSort() {
        return getCustomBoolSort();
    }

    @Override
    public Sort getNullableCustomRealSort() {
        return getCustomRealSort();
    }

    @Override
    public Sort getNullableCustomStringSort() {
        return getCustomStringSort();
    }

    @Override
    public Sort getNullableDateSort() {
        return getDateSort();
    }

    @Override
    public Sort getNullableTimestampSort() {
        return getTimestampSort();
    }

    @Override
    public Expr<UninterpretedSort> mkTimestamp(Timestamp ts) {
        return trackConst(customSorts.getTimestamp(ts));
    }

    @Override
    protected boolean isSortNullable(Sort s) {
        return true;
    }

    @Override
    protected Expr<?> getValueFromMaybeNullable(Expr<?> e) {
        return e;
    }

    @Override
    public BoolExpr mkRawEq(Expr<?> lhs, Expr<?> rhs) {
        return rawEqCache.getUnchecked(new ExprPair(lhs, rhs));
    }

    @Override
    public BoolExpr mkIsSameValue(Expr<?> lhs, Expr<?> rhs) {
        // All sorts from this context are nullable, so this method is the same as `mkRawEq`.
        return mkRawEq(lhs, rhs);
    }

    @Override
    public <S extends Sort> Expr<S> mkNull(S sort) {
        if (!(sort instanceof UninterpretedSort us)) {
            throw new IllegalArgumentException("expecting uninterpreted sort, got: " + sort);
        }
        @SuppressWarnings("unchecked") Expr<S> nullExpr = (Expr<S>) customSorts.mkNull(us);
        return nullExpr;
    }

    @Override
    public BoolExpr mkSqlIsNull(Expr<?> e) {
        return mkRawEq(e, mkNull(e.getSort()));
    }

    @Override
    public UninterpretedSort getCustomIntSort() {
        return customSorts.intSort;
    }

    @Override
    public Expr<UninterpretedSort> mkCustomInt(long value) {
        return trackConst(customSorts.getInt(value));
    }

    @Override
    public Expr<UninterpretedSort> mkCustomInt(BigDecimal value) {
        return trackConst(customSorts.getInt(value));
    }

    @Override
    public BoolExpr mkRawCustomIntLt(Expr<?> left, Expr<?> right) {
        return customSorts.mkRawCustomLt(left, right);
    }

    @Override
    public BoolExpr mkRawStringLike(Expr<?> left, Expr<?> right) {
        return customSorts.mkRawStringLike(left, right);
    }

    @Override
    public UninterpretedSort getCustomRealSort() {
        return customSorts.realSort;
    }

    @Override
    public Expr<UninterpretedSort> mkCustomReal(double value) {
        return trackConst(customSorts.getReal(value));
    }

    @Override
    public UninterpretedSort getCustomStringSort() {
        return customSorts.stringSort;
    }

    @Override
    public UninterpretedSort getCustomBoolSort() {
        return customSorts.boolSort;
    }

    @Override
    public Expr<UninterpretedSort> mkCustomString(String value) {
        return trackConst(customSorts.getString(value));
    }

    @Override
    public Expr<UninterpretedSort> mkCustomBool(boolean value) {
        return trackConst(customSorts.getBool(value));
    }

    @Override
    public <R extends Sort> FuncDecl<R> mkFuncDecl(String s, Sort[] sorts, R sort) {
        return trackFuncDecl(rawContext.mkFuncDecl(s, sorts, sort));
    }

    @Override
    public BoolExpr mkAnd(BoolExpr... boolExprs) {
        BoolExpr res = super.mkAnd(boolExprs);
        if (doSimplify) {
            res = (BoolExpr) res.simplify();
        }
        return res;
    }

    @Override
    public BoolExpr mkOr(BoolExpr... boolExprs) {
        BoolExpr res = super.mkOr(boolExprs);
        if (doSimplify) {
            res = (BoolExpr) res.simplify();
        }
        return res;
    }
}
