package solver.context;

import com.google.common.collect.Iterables;
import com.microsoft.z3.*;

import java.sql.Date;
import java.sql.Timestamp;
import java.util.*;

/**
 * Custom Z3 Context to track constants and use uninterpreted sorts for everything.
 * Assumes that mkSolver is only called after the formula is generated (otherwise,
 * some values may be missing).
 */
public class MyZ3Context {
    final Context rawContext;

    private boolean isTrackingConsts;
    private final HashSet<Expr> untrackedConsts;
    private final HashSet<Expr> trackedConsts;
    private final CustomSorts customSorts;

    public MyZ3Context() {
        this.rawContext = new Context();
        this.isTrackingConsts = false;
        this.untrackedConsts = new HashSet<>();
        this.trackedConsts = new HashSet<>();
        this.customSorts = new CustomSorts(this);
    }

    public Optional<Object> getValueForExpr(Expr e) {
        return customSorts.getValueForExpr(e);
    }

    private <T extends Expr> T trackConstIfNecessary(T c) {
        if (isTrackingConsts && !untrackedConsts.contains(c)) {
            trackedConsts.add(c);
        } else {
            untrackedConsts.add(c);
        }
        return c;
    }

    public BoolExpr mkDistinct(Expr... exprs) {
        return rawContext.mkDistinct(exprs);
    }

    public BoolExpr mkDistinct(Collection<Expr> exprs) {
        return rawContext.mkDistinct(exprs.toArray(new Expr[0]));
    }

    public BoolExpr mkBoolConst(String s) {
        return trackConstIfNecessary(rawContext.mkBoolConst(s));
    }

    public StringSymbol mkSymbol(String s) {
        return rawContext.mkSymbol(s);
    }

    public Expr mkConst(String s, Sort sort) {
        return trackConstIfNecessary(rawContext.mkConst(s, sort));
    }

    public Expr mkFreshConst(String s, Sort sort) {
        return trackConstIfNecessary(rawContext.mkFreshConst(s, sort));
    }

    // Not tracked.
    public Expr mkFreshExistentialConst(String s, Sort sort) {
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

    public void startTrackingConsts() {
        trackedConsts.clear();
        isTrackingConsts = true;
    }

    public void stopTrackingConsts() {
        isTrackingConsts = false;
    }

    public Iterable<Expr> getConsts() {
        return trackedConsts;
    }

    public void customSortsPush() {
        customSorts.push();
    }

    public void customSortsPop() {
        customSorts.pop();
    }

    public String prepareSortDeclaration() {
        return customSorts.prepareSortDeclaration();
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
        return customSorts.getDate(date);
    }

    public Sort getTimestampSort() {
        return customSorts.tsSort;
    }

    public Expr mkTimestamp(Timestamp ts) {
        return customSorts.getTimestamp(ts);
    }

    public Sort getCustomIntSort() {
        return customSorts.intSort;
    }

    public Expr mkCustomInt(long value) {
        return customSorts.getInt(value);
    }

    public Expr mkCustom(Object value) {
        if (value instanceof Long) {
            return mkCustomInt((long) value);
        } else if (value instanceof Integer) {
            return mkCustomInt((int) value);
        } else if (value instanceof String) {
            return mkCustomString((String) value);
        } else if ((value instanceof Float) || (value instanceof Double)) {
            return mkCustomReal((double) value);
        } else if (value instanceof Timestamp) {
            return customSorts.getTimestamp((Timestamp) value);
        } else if (value instanceof Date) {
            return customSorts.getDate((Date) value);
        } else {
            throw new UnsupportedOperationException("object not supported: " + value);
        }
    }

    public BoolExpr mkCustomIntLt(Expr left, Expr right) { return (BoolExpr) customSorts.intLt.apply(left, right); }

    public Sort getCustomRealSort() {
        return customSorts.realSort;
    }

    public Expr mkCustomReal(double value) {
        return customSorts.getReal(value);
    }

    public Sort getCustomStringSort() {
        return customSorts.stringSort;
    }

    public Expr mkCustomString(String value) {
        return customSorts.getString(value);
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

    public FuncDecl mkFreshFuncDecl(String s, Sort[] sorts, Sort sort) {
        return rawContext.mkFreshFuncDecl(s, sorts, sort);
    }
}
