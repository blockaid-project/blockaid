package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.google.common.collect.Lists;
import com.microsoft.z3.*;
import org.apache.calcite.rel.type.RelDataTypeFamily;
import org.apache.calcite.sql.type.SqlTypeFamily;
import org.apache.calcite.sql.type.SqlTypeName;

import java.math.BigDecimal;
import java.sql.Date;
import java.sql.Timestamp;
import java.util.*;
import java.util.function.BiFunction;

import static com.google.common.base.Preconditions.checkState;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.DISABLE_QE;

/**
 * Custom Z3 Context to track constants and use uninterpreted sorts for everything.
 * Assumes that mkSolver is only called after the formula is generated (otherwise,
 * some values may be missing).
 */
public abstract class Z3ContextWrapper<IntegralS extends Sort, RealS extends Sort, StringS extends Sort, BoolS extends Sort> {
    public enum Nullability {
        IS_NULLABLE,
        NOT_NULLABLE
    }

    protected final Context rawContext;
    private final Tactic qeLight;

    public Z3ContextWrapper() {
        this.rawContext = new Context();
        this.qeLight = rawContext.mkTactic("qe-light");
    }

    public static Z3CustomSortsContext makeCustomSortsContext(Set<ContextOption> options) {
        return new Z3CustomSortsContext(options);
    }

    public static Z3ContextWrapper<IntSort, IntSort, IntSort, BoolSort> makeTheoryContext() {
        return new Z3TheoryContext<>();
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
        return rawContext.mkAnd(boolExprs);
    }

    public final BoolExpr mkAnd(Iterable<BoolExpr> boolExprs) {
        return mkAnd(Lists.newArrayList(boolExprs));
    }

    public final BoolExpr mkAnd(List<BoolExpr> boolExprs) {
        return mkAnd(boolExprs.toArray(new BoolExpr[0]));
    }

    public BoolExpr mkOr(BoolExpr... boolExprs) {
        return rawContext.mkOr(boolExprs);
    }

    public final BoolExpr mkOr(List<BoolExpr> boolExprs) {
        return mkOr(boolExprs.toArray(new BoolExpr[0]));
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

    public abstract IntegralS getCustomIntSort(); // Covers both integers and BigDecimal.
    public abstract BoolS getCustomBoolSort();
    public abstract RealS getCustomRealSort();
    public abstract StringS getCustomStringSort();
    public abstract IntegralS getDateSort();
    public abstract IntegralS getTimestampSort();

    // TODO(zhangwen): generics??
    public abstract Sort getNullableCustomIntSort();
    public abstract Sort getNullableCustomBoolSort();
    public abstract Sort getNullableCustomRealSort();
    public abstract Sort getNullableCustomStringSort();
    public abstract Sort getNullableDateSort();
    public abstract Sort getNullableTimestampSort();

    public Sort getCustomIntSort(Nullability o) {
        return switch (o) { case IS_NULLABLE -> getNullableCustomIntSort(); case NOT_NULLABLE -> getCustomIntSort(); };
    }

    public Sort getCustomBoolSort(Nullability o) {
        return switch (o) { case IS_NULLABLE -> getNullableCustomBoolSort(); case NOT_NULLABLE -> getCustomBoolSort(); };
    }

    public Sort getCustomRealSort(Nullability o) {
        return switch (o) { case IS_NULLABLE -> getNullableCustomRealSort(); case NOT_NULLABLE -> getCustomRealSort(); };
    }

    public Sort getCustomStringSort(Nullability o) {
        return switch (o) { case IS_NULLABLE -> getNullableCustomStringSort(); case NOT_NULLABLE -> getCustomStringSort(); };
    }

    public Sort getDateSort(Nullability o) {
        return switch (o) { case IS_NULLABLE -> getNullableDateSort(); case NOT_NULLABLE -> getDateSort(); };
    }

    public Sort getTimestampSort(Nullability o) {
        return switch (o) { case IS_NULLABLE -> getNullableTimestampSort(); case NOT_NULLABLE -> getTimestampSort(); };
    }

    public abstract Expr<IntegralS> mkCustomInt(long value);
    public abstract Expr<IntegralS> mkCustomInt(BigDecimal value);
    public abstract Expr<BoolS> mkCustomBool(boolean value);

    // Assume operands are not nullable.
    public abstract BoolExpr mkRawCustomIntLt(Expr<?> left, Expr<?> right);
    public abstract BoolExpr mkRawStringLike(Expr<?> left, Expr<?> right);

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
        } else if (value instanceof BigDecimal bd) {
            return mkCustomInt(bd);
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
        if (e.isTrue()) {
            return rawContext.mkFalse();
        } else if (e.isFalse()) {
            return rawContext.mkTrue();
        }
        return rawContext.mkNot(e);
    }

    public BoolExpr mkImplies(BoolExpr lhs, BoolExpr rhs) {
        return rawContext.mkImplies(lhs, rhs);
    }

    public BoolExpr mkRawEq(Expr<?> lhs, Expr<?> rhs) {
        return rawContext.mkEq(lhs, rhs);
    }

    protected abstract boolean isSortNullable(Sort s);

    /**
     * Returns the value of a non-null expression of a potentially nullable sort.
     * @param e the expression.
     * @return the value of `e`.
     */
    protected abstract Expr<?> getValueFromMaybeNullable(Expr<?> e);

    /**
     * Makes the null value of the given sort.
     * @param sort the sort of the value to be created; must be a nullable sort.
     * @param <S> the sort type.
     * @return the null value of the given sort.
     */
    public abstract <S extends Sort> Expr<S> mkNull(S sort);

    public abstract BoolExpr mkSqlIsNull(Expr<?> e);

    public BoolExpr mkSqlIsNotNull(Expr<?> e) {
        return rawContext.mkNot(mkSqlIsNull(e));
    }

    // Supports the case where one side is nullable and the other not (in which case, asserts the nullable side is not
    // null and equals the other side).  Treats `null` as the same value as `null`.
    public BoolExpr mkIsSameValue(Expr<?> lhs, Expr<?> rhs) {
        if (lhs.getSort().equals(rhs.getSort())) {
            return mkRawEq(lhs, rhs);
        }
        // One is nullable, the other is not.
        if (isSortNullable(lhs.getSort())) {
            Expr<?> temp = lhs;
            lhs = rhs;
            rhs = temp;
        }
        // LHS is non-nullable, RHS is nullable.
        return rawContext.mkAnd(
                mkSqlIsNotNull(rhs),
                mkRawEq(lhs, getValueFromMaybeNullable(rhs))
        );
    }

    /**
     * Makes a boolean expression for when the SQL predicate "lhs ? rhs" is true.  Takes null into account.
     * @param lhs left-hand side of equality.
     * @param rhs right-hand side of equality.
     * @param op function that generates boolean expression for the binary operation; only applied to expressions of value sort.
     * @return boolean expression.
     */
    private BoolExpr mkSqlBinaryTrue(Expr<?> lhs, Expr<?> rhs, BiFunction<Expr<?>, Expr<?>, BoolExpr> op) {
        return rawContext.mkAnd(
                mkSqlIsNotNull(lhs),
                mkSqlIsNotNull(rhs),
                op.apply(getValueFromMaybeNullable(lhs), getValueFromMaybeNullable(rhs))
        );
    }

    public BoolExpr mkSqlEqTrue(Expr<?> lhs, Expr<?> rhs) {
        return mkSqlBinaryTrue(lhs, rhs, this::mkRawEq);
    }

    public BoolExpr mkSqlNeqTrue(Expr<?> lhs, Expr<?> rhs) {
        return mkSqlBinaryTrue(lhs, rhs, (e1, e2) -> rawContext.mkNot(mkRawEq(e1, e2)));
    }

    public BoolExpr mkCustomIntLtTrue(Expr<?> lhs, Expr<?> rhs) {
        return mkSqlBinaryTrue(lhs, rhs, this::mkRawCustomIntLt);
    }

    public BoolExpr mkCustomIntLteTrue(Expr<?> lhs, Expr<?> rhs) {
        return mkSqlBinaryTrue(lhs, rhs,
                (left, right) -> rawContext.mkOr(mkRawCustomIntLt(left, right), mkRawEq(left, right)));
    }

    public BoolExpr mkStringLikeTrue(Expr<?> lhs, Expr<?> rhs) {
        return mkSqlBinaryTrue(lhs, rhs, this::mkRawStringLike);
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

    // Turns SQL column type to Z3 sort.
    public Sort getSortFromSqlType(SqlTypeName typeName, Nullability nullability) {
        RelDataTypeFamily family = typeName.getFamily();
        if (family == SqlTypeFamily.NUMERIC) {
            // TODO(zhangwen): treating decimal also as int.
            switch (typeName) {
                case TINYINT:
                case SMALLINT:
                case INTEGER:
                case BIGINT:
                case DECIMAL:
                    return getCustomIntSort(nullability);
                case FLOAT:
                case REAL:
                case DOUBLE:
                    return getCustomRealSort(nullability);
            }
            throw new IllegalArgumentException("Unsupported numeric type: " + typeName);
        } else if (family == SqlTypeFamily.CHARACTER || family == SqlTypeFamily.BINARY) {
            return getCustomStringSort(nullability);
        } else if (family == SqlTypeFamily.TIMESTAMP) {
            return getTimestampSort(nullability);
        } else if (family == SqlTypeFamily.DATE) {
            return getDateSort(nullability);
        } else if (family == SqlTypeFamily.BOOLEAN) {
            return getCustomBoolSort(nullability);
        } else if (family == SqlTypeFamily.ANY) {
            // FIXME(zhangwen): I think text belongs in here.
            return getCustomStringSort(nullability);
        }
        throw new IllegalArgumentException("unrecognized family: " + family);
    }
}
