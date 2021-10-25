package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.google.common.collect.Iterables;
import com.microsoft.z3.*;

import java.sql.Date;
import java.sql.Timestamp;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkState;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.DISABLE_QE;

/**
 * Custom Z3 Context to track constants and use uninterpreted sorts for everything.
 * Assumes that mkSolver is only called after the formula is generated (otherwise,
 * some values may be missing).
 */
public abstract class Z3ContextWrapper {
    protected final Context rawContext;
    private final Tactic qeLight;

    public Z3ContextWrapper() {
        this.rawContext = new Context();
        this.qeLight = rawContext.mkTactic("qe-light");
    }

    public static Z3ContextWrapper makeCustomSortsContext(QuantifierOption option) {
        return new Z3CustomSortsContext(option);
    }

    public static Z3ContextWrapper makeTheoryContext() {
        return new Z3TheoryContext();
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

    /**
     * Checks whether two expressions are both constant values and are distinct (i.e., "lhs = rhs" is false).
     * Assumes that if the two expressions have the same type.
     * @param lhs one expression.
     * @param rhs the other expression.
     * @return true if two expressions represent distinct constant values.
     */
    public abstract boolean areDistinctConstants(Expr lhs, Expr rhs);

    public BoolExpr mkDistinct(Expr... exprs) {
        if (exprs.length <= 1) {
            return mkTrue();
        }
        return rawContext.mkDistinct(exprs);
    }

    public BoolExpr mkDistinct(Collection<Expr> exprs) {
        return mkDistinct(exprs.toArray(new Expr[0]));
    }

    public StringSymbol mkSymbol(String s) {
        return rawContext.mkSymbol(s);
    }

    public abstract BoolExpr mkBoolConst(String s);
    public abstract Expr mkConst(String s, Sort sort);
    public abstract Expr mkFreshConst(String s, Sort sort);

    // Not tracked.
    public abstract Expr mkFreshQuantifiedConst(String s, Sort sort);

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

    public abstract void pushTrackConsts();
    public abstract void popTrackConsts();

    // DO NOT track any new consts / func decls while iterating through the returned iterables!
    public abstract TrackedDecls getAllTrackedDecls();
    public abstract String prepareSortDeclaration();

    public abstract String prepareCustomValueConstraints();

    // Return solver without unique constraints on custom sorts; useful when only generating partial
    // SMT formulas.
    public Solver mkRawSolver() {
        return rawContext.mkSolver();
    }

    public abstract Solver mkSolver();
    public abstract Solver mkSolver(Symbol symbol);

    // Make solver for quantifier-free formulas.
    public Solver mkQfSolver() {
        return mkSolver(); // By default, return a regular solver.
    }

    public abstract Sort getCustomIntSort();
    public abstract Sort getCustomBoolSort();
    public abstract Sort getCustomRealSort();
    public abstract Sort getCustomStringSort();
    public abstract Sort getDateSort();
    public abstract Sort getTimestampSort();

    public abstract Expr mkCustomInt(long value);
    public abstract Expr mkCustomBool(boolean value);
    public abstract BoolExpr mkCustomIntLt(Expr left, Expr right);
    public abstract Expr mkCustomString(String value);
    public abstract Expr mkCustomReal(double value);
    public abstract Expr mkDate(Date date);
    public abstract Expr mkTimestamp(Timestamp ts);

    public Expr getExprForValue(Object value) {
        if (value instanceof Long l) {
            return mkCustomInt(l);
        } else if (value instanceof Integer i) {
            return mkCustomInt(i);
        } else if (value instanceof Boolean b) {
            return mkCustomBool(b);
        } else if (value instanceof String s) {
            return mkCustomString(s);
        } else if ((value instanceof Float) || (value instanceof Double)) {
            return mkCustomReal((double) value);
        } else if (value instanceof Timestamp ts) {
            return mkTimestamp(ts);
        } else if (value instanceof Date date) {
            return mkDate(date);
        } else if (value instanceof Expr expr) {
            return expr;
        } else if (value == null) {
            // FIXME(zhangwen): handle NULL properly.
            return null;
        } else {
            throw new UnsupportedOperationException("object not supported: " + value);
        }
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

    public abstract FuncDecl mkFuncDecl(String s, Sort[] sorts, Sort sort);
    public abstract FuncDecl mkFreshFuncDecl(String s, Sort[] sorts, Sort sort);

    public Sort getSortForValue(Object value) {
        if (value instanceof Integer || value instanceof Long) {
            return getCustomIntSort();
        } else if (value instanceof Boolean) {
            return getCustomBoolSort();
        } else if (value instanceof Double) {
            return getCustomRealSort();
        } else if (value instanceof String) {
            return getCustomStringSort();
        } else if (value instanceof Date) {
            return getDateSort();
        } else if (value instanceof Timestamp) {
            return getTimestampSort();
        } else if (value instanceof Expr) {
            return ((Expr) value).getSort();
        } else if (value == null) {
            throw new UnsupportedOperationException("null value unhandled");
        } else {
            throw new UnsupportedOperationException("unknown type for constant loading");
        }
    }
}
