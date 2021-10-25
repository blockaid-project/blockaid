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
class Z3CustomSortsContext extends Z3ContextWrapper{
    private final ArrayList<BaseTrackedDecls> trackedDeclStack;
    private final CustomSorts customSorts;

    Z3CustomSortsContext(QuantifierOption option) {
        this.trackedDeclStack = new ArrayList<>();
        trackedDeclStack.add(new BaseTrackedDecls());
        this.customSorts = new CustomSorts(this, option);
    }

    @Override
    public boolean areDistinctConstants(Expr lhs, Expr rhs) {
        Optional<Object> lhsV = customSorts.getValueForExpr(lhs), rhsV = customSorts.getValueForExpr(rhs);
        return lhsV.isPresent() && rhsV.isPresent() && !lhsV.get().equals(rhsV.get());
    }

    private <T extends Expr> T trackConst(T c) {
        for (BaseTrackedDecls decls : trackedDeclStack) {
            if (decls.containsConst(c)) {
                return c;
            }
        }
        trackedDeclStack.get(trackedDeclStack.size() - 1).addConst(c);
        return c;
    }

    private FuncDecl trackFuncDecl(FuncDecl f) {
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
    public Expr mkConst(String s, Sort sort) {
        return trackConst(rawContext.mkConst(s, sort));
    }

    @Override
    public Expr mkFreshConst(String s, Sort sort) {
        return trackConst(rawContext.mkFreshConst(s, sort));
    }

    // Not tracked.
    @Override
    public Expr mkFreshQuantifiedConst(String s, Sort sort) {
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
    public Sort getDateSort() {
        return customSorts.dateSort;
    }

    @Override
    public Expr mkDate(Date date) {
        return trackConst(customSorts.getDate(date));
    }

    @Override
    public Sort getTimestampSort() {
        return customSorts.tsSort;
    }

    @Override
    public Expr mkTimestamp(Timestamp ts) {
        return trackConst(customSorts.getTimestamp(ts));
    }

    @Override
    public Sort getCustomIntSort() {
        return customSorts.intSort;
    }

    @Override
    public Expr mkCustomInt(long value) {
        return trackConst(customSorts.getInt(value));
    }

    @Override
    public BoolExpr mkCustomIntLt(Expr left, Expr right) {
        return (BoolExpr) customSorts.intLt.apply(left, right);
    }

    @Override
    public Sort getCustomRealSort() {
        return customSorts.realSort;
    }

    @Override
    public Expr mkCustomReal(double value) {
        return trackConst(customSorts.getReal(value));
    }

    @Override
    public Sort getCustomStringSort() {
        return customSorts.stringSort;
    }

    @Override
    public Sort getCustomBoolSort() {
        return customSorts.boolSort;
    }

    @Override
    public Expr mkCustomString(String value) {
        return trackConst(customSorts.getString(value));
    }

    @Override
    public Expr mkCustomBool(boolean value) {
        return trackConst(customSorts.getBool(value));
    }

    @Override
    public FuncDecl mkFuncDecl(String s, Sort[] sorts, Sort sort) {
        return trackFuncDecl(rawContext.mkFuncDecl(s, sorts, sort));
    }

    @Override
    public FuncDecl mkFreshFuncDecl(String s, Sort[] sorts, Sort sort) {
        return trackFuncDecl(rawContext.mkFreshFuncDecl(s, sorts, sort));
    }
}
