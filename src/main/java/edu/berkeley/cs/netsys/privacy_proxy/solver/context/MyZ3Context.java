package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.google.common.collect.Iterables;
import com.microsoft.z3.*;

import java.sql.Date;
import java.sql.Timestamp;
import java.util.*;

import static com.google.common.base.Preconditions.checkState;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.DISABLE_QE;

/**
 * Custom Z3 Context to track constants and use uninterpreted sorts for everything.
 * Assumes that mkSolver is only called after the formula is generated (otherwise,
 * some values may be missing).
 */
public class MyZ3Context {
    final Context rawContext;
    private final Tactic qeLight;

    private final ArrayList<BaseTrackedDecls> trackedDeclStack;
    private final CustomSorts customSorts;

    public MyZ3Context() {
        this.rawContext = new Context();
        this.qeLight = rawContext.mkTactic("qe-light");
        this.trackedDeclStack = new ArrayList<>();
        trackedDeclStack.add(new BaseTrackedDecls());
        this.customSorts = new CustomSorts(this);
    }

    public BoolExpr eliminateQuantifiers(BoolExpr e) {
        if (DISABLE_QE) {
            return e;
        }

        Goal g = rawContext.mkGoal(false, false, false);
        g.add(e);
        ApplyResult res = qeLight.apply(g);
        checkState(res.getNumSubgoals() == 1);
        return res.getSubgoals()[0].AsBoolExpr();
    }

    public Optional<Object> getValueForExpr(Expr e) {
        return customSorts.getValueForExpr(e);
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

    public BoolExpr mkDistinct(Expr... exprs) {
        if (exprs.length <= 1) {
            return mkTrue();
        }
        return rawContext.mkDistinct(exprs);
    }

    public BoolExpr mkDistinct(Collection<Expr> exprs) {
        return mkDistinct(exprs.toArray(new Expr[0]));
    }

    public BoolExpr mkBoolConst(String s) {
        return trackConst(rawContext.mkBoolConst(s));
    }

    public StringSymbol mkSymbol(String s) {
        return rawContext.mkSymbol(s);
    }

    public Expr mkConst(String s, Sort sort) {
        return trackConst(rawContext.mkConst(s, sort));
    }

    public Expr mkFreshConst(String s, Sort sort) {
        return trackConst(rawContext.mkFreshConst(s, sort));
    }

    // Not tracked.
    public Expr mkFreshQuantifiedConst(String s, Sort sort) {
        return rawContext.mkFreshConst(s, sort);
    }

    public BoolExpr mkAnd(BoolExpr... boolExprs) {
        if (boolExprs.length == 0) {
            return rawContext.mkTrue();
        }
        if (boolExprs.length == 1) {
            return boolExprs[0];
        }
        for (BoolExpr boolExpr : boolExprs) {
            if (boolExpr.isFalse()) {
                return rawContext.mkFalse();
            }
        }
        return rawContext.mkAnd(boolExprs);
    }

    public BoolExpr mkAnd(Iterable<BoolExpr> boolExprs) {
        return mkAnd(Iterables.toArray(boolExprs, BoolExpr.class));
    }

    public BoolExpr mkOr(BoolExpr... boolExprs) {
        return rawContext.mkOr(boolExprs);
    }

    public BoolExpr myMkForall(Collection<Expr> quantifiers, BoolExpr body) {
        return myMkForall(quantifiers.toArray(new Expr[0]), body);
    }

    public BoolExpr myMkForall(Expr[] quantifiers, BoolExpr body) {
        if (quantifiers.length == 0) {
            return body;
        }
        return rawContext.mkForall(quantifiers, body, 1, null, null, null, null);
    }

    public BoolExpr myMkExists(Collection<Expr> quantifiers, BoolExpr body) {
        if (quantifiers.isEmpty()) {
            return body;
        }
        return rawContext.mkExists(quantifiers.toArray(new Expr[0]), body, 1, null, null, null, null);
    }

    public void pushTrackConsts() {
        customSorts.push();
        trackedDeclStack.add(new BaseTrackedDecls());
    }

    public void popTrackConsts() {
        trackedDeclStack.remove(trackedDeclStack.size() - 1);
        customSorts.pop();
    }

    // DO NOT track any new consts / func decls while iterating through the returned iterables!
    public TrackedDecls getAllTrackedDecls() {
        return new MergedTrackedDecls(trackedDeclStack);
    }
//
//    public void customSortsPush() {
//        customSorts.push();
//    }
//
//    public void customSortsPop() {
//        customSorts.pop();
//    }

    public String prepareSortDeclaration() {
        return customSorts.prepareSortDeclaration();
    }

    public String prepareCustomValueConstraints() {
        return customSorts.prepareCustomValueConstraints();
    }

    // Return solver without unique constraints on custom sorts; useful when only generating partial
    // SMT formulas.
    public Solver mkRawSolver() {
        return rawContext.mkSolver();
    }

    public Solver mkSolver() {
        return customSorts.prepareSolver(rawContext.mkSolver());
    }

    public Solver mkSolver(Symbol symbol) {
        return customSorts.prepareSolver(rawContext.mkSolver(symbol));
    }

    public Sort getDateSort() {
        return customSorts.dateSort;
    }

    public Expr mkDate(Date date) {
        return trackConst(customSorts.getDate(date));
    }

    public Sort getTimestampSort() {
        return customSorts.tsSort;
    }

    public Expr mkTimestamp(Timestamp ts) {
        return trackConst(customSorts.getTimestamp(ts));
    }

    public Sort getCustomIntSort() {
        return customSorts.intSort;
    }

    public Expr mkCustomInt(long value) {
        return trackConst(customSorts.getInt(value));
    }

    public Expr mkCustom(Object value) {
        Expr e;
        if (value instanceof Long) {
            e = mkCustomInt((long) value);
        } else if (value instanceof Integer) {
            e = mkCustomInt((int) value);
        } else if (value instanceof String) {
            e = mkCustomString((String) value);
        } else if ((value instanceof Float) || (value instanceof Double)) {
            e = mkCustomReal((double) value);
        } else if (value instanceof Timestamp) {
            e = customSorts.getTimestamp((Timestamp) value);
        } else if (value instanceof Date) {
            e = customSorts.getDate((Date) value);
        } else {
            throw new UnsupportedOperationException("object not supported: " + value);
        }
        return trackConst(e);
    }

    public BoolExpr mkCustomIntLt(Expr left, Expr right) { return (BoolExpr) customSorts.intLt.apply(left, right); }

    public Sort getCustomRealSort() {
        return customSorts.realSort;
    }

    public Expr mkCustomReal(double value) {
        return trackConst(customSorts.getReal(value));
    }

    public Sort getCustomStringSort() {
        return customSorts.stringSort;
    }

    public Sort getCustomBoolSort() {
        return customSorts.boolSort;
    }

    public Expr mkCustomString(String value) {
        return trackConst(customSorts.getString(value));
    }

    public Expr mkCustomBool(boolean value) {
        return trackConst(customSorts.getBool(value));
    }

    public BoolExpr mkNot(BoolExpr e) {
        return rawContext.mkNot(e);
    }

    public BoolExpr mkImplies(BoolExpr lhs, BoolExpr rhs) {
        return rawContext.mkImplies(lhs, rhs);
    }

    public BoolExpr mkEq(Expr lhs, Expr rhs) {
        return rawContext.mkEq(lhs, rhs);
    }

    public BoolExpr mkAtMost(Collection<BoolExpr> exprs, int bound) {
        return rawContext.mkAtMost(exprs.toArray(new BoolExpr[0]), bound);
    }

    public BoolExpr mkAtLeast(Collection<BoolExpr> exprs, int bound) {
        return rawContext.mkAtLeast(exprs.toArray(new BoolExpr[0]), bound);
    }

    public Params mkParams() {
        return rawContext.mkParams();
    }

    public BoolExpr mkTrue() {
        return rawContext.mkTrue();
    }

    public BoolExpr mkFalse() {
        return rawContext.mkFalse();
    }

    public BoolSort getBoolSort() {
        return rawContext.getBoolSort();
    }

    public BoolExpr mkBool(boolean b) {
        return rawContext.mkBool(b);
    }

    public FuncDecl mkFuncDecl(String s, Sort[] sorts, Sort sort) {
        return trackFuncDecl(rawContext.mkFuncDecl(s, sorts, sort));
    }

    public FuncDecl mkFreshFuncDecl(String s, Sort[] sorts, Sort sort) {
        return trackFuncDecl(rawContext.mkFreshFuncDecl(s, sorts, sort));
    }
}
