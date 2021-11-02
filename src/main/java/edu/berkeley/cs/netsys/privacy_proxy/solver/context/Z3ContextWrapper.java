package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.google.common.collect.Lists;
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
public abstract class Z3ContextWrapper<IntegralS extends Sort, RealS extends Sort, StringS extends Sort, BoolS extends Sort> {
    protected final Context rawContext;
    private final Tactic qeLight;

    public Z3ContextWrapper() {
        this.rawContext = new Context();
        this.qeLight = rawContext.mkTactic("qe-light");
    }

    public static Z3ContextWrapper<UninterpretedSort, UninterpretedSort, UninterpretedSort, UninterpretedSort> makeCustomSortsContext(QuantifierOption option) {
        return new Z3CustomSortsContext(option);
    }

    public static Z3ContextWrapper<IntSort, IntSort, IntSort, BoolSort> makeTheoryContext() {
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
    public abstract boolean areDistinctConstants(Expr<?> lhs, Expr<?> rhs);

    public BoolExpr mkDistinct(Expr<?>... exprs) {
        if (exprs.length <= 1) {
            return mkTrue();
        }
        return rawContext.mkDistinct(exprs);
    }

    public <S extends Sort> BoolExpr mkDistinct(Collection<Expr<S>> exprs) {
        return mkDistinct(exprs.toArray(new Expr[0]));
    }

    public BoolExpr mkDistinctUntyped(Collection<Expr<?>> exprs) {
        return mkDistinct(exprs.toArray(new Expr[0]));
    }

    public abstract BoolExpr mkBoolConst(String s);
    public abstract <S extends Sort> Expr<S> mkConst(String s, S sort);
    public abstract <S extends Sort> Expr<S> mkFreshConst(String s, S sort);

    // Not tracked.
    public abstract <S extends Sort> Expr<S> mkFreshQuantifiedConst(String s, S sort);

    public BoolExpr mkAnd(BoolExpr... boolExprs) {
        return mkAnd(Arrays.asList(boolExprs));
    }

    public BoolExpr mkAnd(Iterable<BoolExpr> boolExprs) {
        return mkAnd(Lists.newArrayList(boolExprs));
    }

    public BoolExpr mkAnd(List<BoolExpr> boolExprs) {
        if (boolExprs.isEmpty()) {
            return rawContext.mkTrue();
        }
        if (boolExprs.size() == 1) {
            return boolExprs.get(0);
        }

        for (BoolExpr boolExpr : boolExprs) {
            if (boolExpr.isFalse()) {
                return rawContext.mkFalse();
            }
        }

        return rawContext.mkAnd(boolExprs.toArray(new BoolExpr[0]));
    }

    public BoolExpr mkAnd(BoolExpr e1, BoolExpr e2) {
        return mkAnd(List.of(e1, e2));
    }

    public BoolExpr mkOr(List<BoolExpr> boolExprs) {
        return rawContext.mkOr(boolExprs.toArray(new BoolExpr[0]));
    }

    public BoolExpr mkOr(BoolExpr... boolExprs) {
        return rawContext.mkOr(boolExprs);
    }

    public BoolExpr myMkForall(Collection<Expr<?>> quantifiers, BoolExpr body) {
        return myMkForall(quantifiers.toArray(new Expr[0]), body);
    }

    public BoolExpr myMkForall(Expr<?>[] quantifiers, BoolExpr body) {
        if (quantifiers.length == 0) {
            return body;
        }
        return rawContext.mkForall(quantifiers, body, 1, null, null, null, null);
    }

    public BoolExpr myMkExists(Collection<Expr<?>> quantifiers, BoolExpr body) {
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

    public abstract IntegralS getCustomIntSort();
    public abstract BoolS getCustomBoolSort();
    public abstract RealS getCustomRealSort();
    public abstract StringS getCustomStringSort();
    public abstract IntegralS getDateSort();
    public abstract IntegralS getTimestampSort();

    public abstract Expr<IntegralS> mkCustomInt(long value);
    public abstract Expr<BoolS> mkCustomBool(boolean value);
    public abstract BoolExpr mkCustomIntLt(Expr<?> left, Expr<?> right);
    public abstract Expr<StringS> mkCustomString(String value);
    public abstract Expr<RealS> mkCustomReal(double value);
    public abstract Expr<IntegralS> mkDate(Date date);
    public abstract Expr<IntegralS> mkTimestamp(Timestamp ts);

    public Expr<?> getExprForValue(Object value) {
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

    public BoolExpr mkEq(Expr<?> lhs, Expr<?> rhs) {
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

    public abstract <R extends Sort> FuncDecl<R> mkFuncDecl(String s, Sort[] sorts, R sort);
    public abstract <R extends Sort> FuncDecl<R> mkFreshFuncDecl(String s, Sort[] sorts, R sort);

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
        } else if (value == null) {
            throw new UnsupportedOperationException("null value unhandled");
        } else {
            throw new UnsupportedOperationException("unknown type for constant loading");
        }
    }
}
