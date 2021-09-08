package solver;

import com.google.common.collect.Iterables;
import com.microsoft.z3.*;

import java.sql.Date;
import java.sql.Timestamp;
import java.util.*;
import java.util.function.Function;

/**
 * Custom Z3 Context to track constants and use uninterpreted sorts for everything.
 * Assumes that mkSolver is only called after the formula is generated (otherwise,
 * some values may be missing).
 */
public class MyZ3Context extends Context {
    private boolean isTrackingConsts;
    private final HashSet<Expr> untrackedConsts;
    private final HashSet<Expr> trackedConsts;
    private final CustomSorts customSorts;

    private final Map<Sort, Map<String, Expr>> constCache = new HashMap<>();

    private class CustomSorts {
        private final Sort dateSort;
        private final Sort tsSort;
        private final Sort intSort;
        private final Sort realSort;
        private final Sort stringSort;
        private final List<Values> valuesStack;

        private final FuncDecl intLt;

        private class Values {
            private final Map<Date, Expr> dateValues = new HashMap<>();
            private final Map<Timestamp, Expr> tsValues = new HashMap<>();
            private final Map<Long, Expr> intValues = new HashMap<>();
            private final Map<Double, Expr> realValues = new HashMap<>();
            private final Map<String, Expr> stringValues = new HashMap<>();

            private final Map<Expr, Object> expr2Obj = new HashMap<>();
        }

        private CustomSorts() {
            MyZ3Context ctx = MyZ3Context.this;

            intSort = ctx.mkUninterpretedSort("CS!INT");
//            dateSort = ctx.mkUninterpretedSort("CS!DATE");
//            tsSort = ctx.mkUninterpretedSort("CS!TS");
            dateSort = intSort;
            tsSort = intSort;
            realSort = ctx.mkUninterpretedSort("CS!REAL");
            stringSort = ctx.mkUninterpretedSort("CS!STRING");
            valuesStack = new ArrayList<>();
            valuesStack.add(new Values());

            intLt = ctx.mkFuncDecl("lt", new Sort[]{intSort, intSort}, ctx.getBoolSort());
//            {
//                Expr x = mkConst("x", intSort), y = mkConst("y", intSort), z = mkConst("z", intSort);
//                BoolExpr trans = mkForall(
//                        new Expr[]{x, y, z},
//                        mkImplies(
//                                mkAnd((BoolExpr) intLt.apply(x, y), (BoolExpr) intLt.apply(y, z)),
//                                (BoolExpr) intLt.apply(x, z)
//                        ), 1, null, null, null, null
//                );
//                intLtAxioms = ImmutableList.of(trans);
//            }
        }

        private void push() {
            valuesStack.add(new Values());
        }

        private void pop() {
            valuesStack.remove(valuesStack.size() - 1);
        }

        private Expr getDate(Date date) {
            for (int i = valuesStack.size(); i-- > 0; ) {
                if (valuesStack.get(i).dateValues.containsKey(date)) {
                    return valuesStack.get(i).dateValues.get(date);
                }
            }
            Expr c = mkFreshConst(dateSort.getSExpr(), dateSort);
            Values vs = valuesStack.get(valuesStack.size() - 1);
            vs.dateValues.put(date, c);
            vs.expr2Obj.put(c, date);
            return c;
        }

        private Expr getTimestamp(Timestamp ts) {
            for (int i = valuesStack.size(); i-- > 0; ) {
                if (valuesStack.get(i).tsValues.containsKey(ts)) {
                    return valuesStack.get(i).tsValues.get(ts);
                }
            }
            Expr c = mkFreshConst(tsSort.getSExpr(), tsSort);
            Values vs = valuesStack.get(valuesStack.size() - 1);
            vs.tsValues.put(ts, c);
            vs.expr2Obj.put(c, ts);
            return c;
        }

        private Expr getInt(long value) {
            for (int i = valuesStack.size(); i-- > 0; ) {
                if (valuesStack.get(i).intValues.containsKey(value)) {
                    return valuesStack.get(i).intValues.get(value);
                }
            }
            Expr c = mkFreshConst(intSort.getSExpr(), intSort);
            Values vs = valuesStack.get(valuesStack.size() - 1);
            vs.intValues.put(value, c);
            vs.expr2Obj.put(c, value);
            return c;
        }

        private Expr getReal(double value) {
            for (int i = valuesStack.size(); i-- > 0; ) {
                if (valuesStack.get(i).realValues.containsKey(value)) {
                    return valuesStack.get(i).realValues.get(value);
                }
            }
            Expr c = mkFreshConst(realSort.getSExpr(), realSort);
            Values vs = valuesStack.get(valuesStack.size() - 1);
            vs.realValues.put(value, c);
            vs.expr2Obj.put(c, value);
            return c;
        }

        private Expr getString(String value) {
            for (int i = valuesStack.size(); i-- > 0; ) {
                if (valuesStack.get(i).stringValues.containsKey(value)) {
                    return valuesStack.get(i).stringValues.get(value);
                }
            }
            Expr c = mkFreshConst(stringSort.getSExpr(), stringSort);
            Values vs = valuesStack.get(valuesStack.size() - 1);
            vs.stringValues.put(value, c);
            vs.expr2Obj.put(c, value);
            return c;
        }

        private Optional<Object> getValueForExpr(Expr e) {
            for (int i = valuesStack.size(); i-- > 0; ) {
                Values vs = valuesStack.get(i);
                if (vs.expr2Obj.containsKey(e)) {
                    return Optional.of(vs.expr2Obj.get(e));
                }
            }
            return Optional.empty();
        }

        private <T extends Comparable<? super T>> Collection<BoolExpr> mkLtConstraints(Map<T, Expr> exprs) {
            if (exprs.size() <= 1) {
                return Collections.emptyList();
            }

            ArrayList<T> keys = new ArrayList<>(exprs.keySet());
            Collections.sort(keys);
            ArrayList<BoolExpr> res = new ArrayList<>();
            // Encodes transitivity of less-than.  Should use a forall axiom, but that breaks QF bounded formulas.
            for (int i = 0; i < keys.size(); ++i) {
                Expr thisElem = exprs.get(keys.get(i));
                for (int j = i + 1; j < keys.size(); ++j) {
                    Expr otherElem = exprs.get(keys.get(j));
                    res.add((BoolExpr) intLt.apply(thisElem, otherElem));
                }
            }
            return res;
        }

        // Prepares Solver for use with custom sorts (adds uniqueness constraints)
        private Solver prepareSolver(Solver solver) {
            if (solver.getNumAssertions() > 0) {
                return solver;
            }
            Map<Date, Expr> dateValues = valuesStack.stream().reduce(new HashMap<>(), (m, v) -> { m.putAll(v.dateValues); return m; }, (m1, m2) -> { m1.putAll(m2); return m1; });
            if (dateValues.size() > 1) {
                solver.add(mkDistinct(dateValues.values().toArray(new Expr[0])));
                solver.add(mkLtConstraints(dateValues).toArray(new BoolExpr[0]));
            }
            Map<Timestamp, Expr> tsValues = valuesStack.stream().reduce(new HashMap<>(), (m, v) -> { m.putAll(v.tsValues); return m; }, (m1, m2) -> { m1.putAll(m2); return m1; });
            if (tsValues.size() > 1) {
                solver.add(mkDistinct(tsValues.values().toArray(new Expr[0])));
                solver.add(mkLtConstraints(tsValues).toArray(new BoolExpr[0]));
            }
            Map<Long, Expr> intValues = valuesStack.stream().reduce(new HashMap<>(), (m, v) -> { m.putAll(v.intValues); return m; }, (m1, m2) -> { m1.putAll(m2); return m1; });
            if (intValues.size() > 1) {
                solver.add(mkDistinct(intValues.values().toArray(new Expr[0])));
                solver.add(mkLtConstraints(intValues).toArray(new BoolExpr[0]));
            }
            Map<Double, Expr> realValues = valuesStack.stream().reduce(new HashMap<>(), (m, v) -> { m.putAll(v.realValues); return m; }, (m1, m2) -> { m1.putAll(m2); return m1; });
            if (realValues.size() > 1) {
                solver.add(mkDistinct(realValues.values().toArray(new Expr[0])));
            }
            Map<String, Expr> stringValues = valuesStack.stream().reduce(new HashMap<>(), (m, v) -> { m.putAll(v.stringValues); return m; }, (m1, m2) -> { m1.putAll(m2); return m1; });
            if (stringValues.size() > 1) {
                solver.add(mkDistinct(stringValues.values().toArray(new Expr[0])));
            }
//            solver.add(intLtAxioms.toArray(new BoolExpr[0]));
            return solver;
        }

        private String prepareSortDeclaration() {
            // Reusing prepareSolver is messy - some constants and sorts may not be used/declared.
            StringBuilder sb = new StringBuilder();
//            sb.append("(declare-sort ").append(dateSort.getSExpr()).append(" 0)\n");
//            sb.append("(declare-sort ").append(tsSort.getSExpr()).append(" 0)\n");
            sb.append("(declare-sort ").append(realSort.getSExpr()).append(" 0)\n");
            sb.append("(declare-sort ").append(stringSort.getSExpr()).append(" 0)\n");
            sb.append("(declare-sort ").append(intSort.getSExpr()).append(" 0)\n");

            sb.append(intLt.getSExpr()).append("\n");
//            for (BoolExpr e : intLtAxioms) {
//                sb.append("(assert ").append(e.getSExpr()).append(")\n");
//            }

            prepareSortValuesComparable(sb, v -> v.dateValues);
            prepareSortValuesComparable(sb, v -> v.tsValues);
            prepareSortValuesComparable(sb, v -> v.intValues);
            prepareSortValues(sb, v -> v.realValues);
            prepareSortValues(sb, v -> v.stringValues);
            return sb.toString();
        }

        private <T> void prepareSortValues(StringBuilder sb, Function<Values, Map<T, Expr>> valueMapPicker) {
            StringBuilder distinct = new StringBuilder("(assert (distinct");
            int numValues = 0;

            for (Values vs : valuesStack) {
                for (Map.Entry<T, Expr> entry : valueMapPicker.apply(vs).entrySet()) {
                    Expr expr = entry.getValue();
                    sb.append(String.format("(declare-fun %s () %s)  ; %s\n",
                            expr.getSExpr(), expr.getSort().getSExpr(),
                            entry.getKey().toString().replace("\n", "")));
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
                StringBuilder sb, Function<Values, Map<T, Expr>> valueMapPicker) {
            prepareSortValues(sb, valueMapPicker);
            Map<T, Expr> value2Expr = valuesStack.stream().reduce(new HashMap<>(), (m, v) -> { m.putAll(valueMapPicker.apply(v)); return m; }, (m1, m2) -> { m1.putAll(m2); return m1; });
            for (BoolExpr e : mkLtConstraints(value2Expr)) {
                sb.append("(assert ").append(e.getSExpr()).append(")\n");
            }
        }
    }

    public MyZ3Context() {
        super();
        isTrackingConsts = false;
        untrackedConsts = new HashSet<>();
        trackedConsts = new HashSet<>();
        customSorts = new CustomSorts();
    }

    public Optional<Object> getValueForExpr(Expr e) {
        return customSorts.getValueForExpr(e);
    }

    @Override
    public Expr mkConst(String s, Sort sort) {
        Expr c = super.mkConst(s, sort);
        if (isTrackingConsts && !untrackedConsts.contains(c)) {
            trackedConsts.add(c);
        } else {
            untrackedConsts.add(c);
        }
        return c;
    }

    @Override
    public Expr mkFreshConst(String s, Sort sort) {
        Expr c = super.mkFreshConst(s, sort);
        if (isTrackingConsts && !untrackedConsts.contains(c)) {
            trackedConsts.add(c);
        } else {
            untrackedConsts.add(c);
        }
        return c;
    }

    @Override
    public BoolExpr mkAnd(BoolExpr... boolExprs) {
        if (boolExprs.length == 0) {
            return mkTrue();
        }
        if (boolExprs.length == 1) {
            return boolExprs[0];
        }
        for (BoolExpr boolExpr : boolExprs) {
            if (boolExpr.isFalse()) {
                return mkFalse();
            }
        }
        return super.mkAnd(boolExprs);
    }

    public BoolExpr mkAnd(Iterable<BoolExpr> boolExprs) {
        return mkAnd(Iterables.toArray(boolExprs, BoolExpr.class));
    }

    public BoolExpr myMkExists(Collection<Expr> quantifiers, BoolExpr body) {
        if (quantifiers.isEmpty()) {
            return body;
        }
        return mkExists(quantifiers.toArray(new Expr[0]), body, 1, null, null, null, null);
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
        return super.mkSolver();
    }

    @Override
    public Solver mkSolver() {
        return customSorts.prepareSolver(super.mkSolver());
    }

    @Override
    public Solver mkSolver(Symbol symbol) {
        return customSorts.prepareSolver(super.mkSolver(symbol));
    }

    @Override
    public Solver mkSolver(String s) {
        return customSorts.prepareSolver(super.mkSolver(s));
    }

    @Override
    public Solver mkSimpleSolver() {
        return customSorts.prepareSolver(super.mkSimpleSolver());
    }

    @Override
    public Solver mkSolver(Tactic tactic) {
        return customSorts.prepareSolver(super.mkSolver(tactic));
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

    // Overrides to deprecate Z3's standard sorts where we have custom uninterpreted sorts.
    @Override
    @Deprecated
    public IntSort getIntSort() {
        return super.getIntSort();
    }

    @Override
    @Deprecated
    public IntSort mkIntSort() {
        return super.mkIntSort();
    }

    @Override
    @Deprecated
    public IntExpr mkIntConst(Symbol symbol) {
        return super.mkIntConst(symbol);
    }

    @Override
    @Deprecated
    public IntExpr mkIntConst(String s) {
        return super.mkIntConst(s);
    }

    @Override
    @Deprecated
    public IntNum mkInt(String s) {
        return super.mkInt(s);
    }

    @Override
    @Deprecated
    public IntNum mkInt(int i) {
        return super.mkInt(i);
    }

    @Override
    @Deprecated
    public IntNum mkInt(long l) {
        return super.mkInt(l);
    }

    public Sort getCustomRealSort() {
        return customSorts.realSort;
    }

    public Expr mkCustomReal(double value) {
        return customSorts.getReal(value);
    }

    @Override
    @Deprecated
    public RealSort getRealSort() {
        return super.getRealSort();
    }

    @Override
    @Deprecated
    public RealSort mkRealSort() {
        return super.mkRealSort();
    }

    @Override
    @Deprecated
    public RealExpr mkRealConst(Symbol symbol) {
        return super.mkRealConst(symbol);
    }

    @Override
    @Deprecated
    public RealExpr mkRealConst(String s) {
        return super.mkRealConst(s);
    }

    @Override
    @Deprecated
    public RatNum mkReal(int i, int i1) {
        return super.mkReal(i, i1);
    }

    @Override
    @Deprecated
    public RatNum mkReal(String s) {
        return super.mkReal(s);
    }

    @Override
    @Deprecated
    public RatNum mkReal(int i) {
        return super.mkReal(i);
    }

    @Override
    @Deprecated
    public RatNum mkReal(long l) {
        return super.mkReal(l);
    }

    public Sort getCustomStringSort() {
        return customSorts.stringSort;
    }

    public Expr mkCustomString(String value) {
        return customSorts.getString(value);
    }

    @Override
    @Deprecated
    public SeqSort getStringSort() {
        return super.getStringSort();
    }

    @Override
    @Deprecated
    public SeqSort mkStringSort() {
        return super.mkStringSort();
    }

    @Override
    @Deprecated
    public SeqExpr mkString(String s) {
        return super.mkString(s);
    }
}
