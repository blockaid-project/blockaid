package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.microsoft.z3.*;

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

    Z3CustomSortsContext(QuantifierOption option) {
        this.trackedDeclStack = new ArrayList<>();
        trackedDeclStack.add(new BaseTrackedDecls());
        this.customSorts = new CustomSorts(this, option);
    }

    @Override
    public boolean areDistinctConstants(Expr<?> lhs, Expr<?> rhs) {
        Optional<Object> lhsV = customSorts.getValueForExpr(lhs), rhsV = customSorts.getValueForExpr(rhs);
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
    public Expr<UninterpretedSort> mkTimestamp(Timestamp ts) {
        return trackConst(customSorts.getTimestamp(ts));
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
    public BoolExpr mkCustomIntLt(Expr<?> left, Expr<?> right) {
        return (BoolExpr) customSorts.intLt.apply(left, right);
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
    public <R extends Sort> FuncDecl<R> mkFreshFuncDecl(String s, Sort[] sorts, R sort) {
        return trackFuncDecl(rawContext.mkFreshFuncDecl(s, sorts, sort));
    }
}
