package solver;

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

    private class CustomSorts {
        private final Sort dateSort;
        private final Sort tsSort;
        private final Sort intSort;
        private final Sort realSort;
        private final Sort stringSort;
        private final List<Values> valuesStack;

        private final FuncDecl intLt;

        private class Values {
            private final Map<Date, Expr> dateValues;
            private final Map<Timestamp, Expr> tsValues;
            private final Map<Long, Expr> intValues;
            private final Map<Double, Expr> realValues;
            private final Map<String, Expr> stringValues;

            private Values() {
                dateValues = new HashMap<>();
                tsValues = new HashMap<>();
                intValues = new HashMap<>();
                realValues = new HashMap<>();
                stringValues = new HashMap<>();
            }
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

            intLt = ctx.mkFreshFuncDecl("lt", new Sort[]{intSort, intSort}, ctx.getBoolSort());
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
            valuesStack.get(valuesStack.size() - 1).dateValues.put(date, c);
            return c;
        }

        private Expr getTimestamp(Timestamp ts) {
            for (int i = valuesStack.size(); i-- > 0; ) {
                if (valuesStack.get(i).tsValues.containsKey(ts)) {
                    return valuesStack.get(i).tsValues.get(ts);
                }
            }
            Expr c = mkFreshConst(tsSort.getSExpr(), tsSort);
            valuesStack.get(valuesStack.size() - 1).tsValues.put(ts, c);
            return c;
        }

        private Expr getInt(long value) {
            for (int i = valuesStack.size(); i-- > 0; ) {
                if (valuesStack.get(i).intValues.containsKey(value)) {
                    return valuesStack.get(i).intValues.get(value);
                }
            }
            Expr c = mkFreshConst(intSort.getSExpr(), intSort);
            valuesStack.get(valuesStack.size() - 1).intValues.put(value, c);
            return c;
        }

        private Expr getReal(double value) {
            for (int i = valuesStack.size(); i-- > 0; ) {
                if (valuesStack.get(i).realValues.containsKey(value)) {
                    return valuesStack.get(i).realValues.get(value);
                }
            }
            Expr c = mkFreshConst(realSort.getSExpr(), realSort);
            valuesStack.get(valuesStack.size() - 1).realValues.put(value, c);
            return c;
        }

        private Expr getString(String value) {
            for (int i = valuesStack.size(); i-- > 0; ) {
                if (valuesStack.get(i).stringValues.containsKey(value)) {
                    return valuesStack.get(i).stringValues.get(value);
                }
            }
            Expr c = mkFreshConst(stringSort.getSExpr(), stringSort);
            valuesStack.get(valuesStack.size() - 1).stringValues.put(value, c);
            return c;
        }

        // Prepares Solver for use with custom sorts (adds uniqueness constraints)
        private Solver prepareSolver(Solver solver) {
            if (solver.getNumAssertions() > 0) {
                return solver;
            }
            Map<Date, Expr> dateValues = valuesStack.stream().reduce(new HashMap<>(), (m, v) -> { m.putAll(v.dateValues); return m; }, (m1, m2) -> { m1.putAll(m2); return m1; });
            if (dateValues.size() > 1) {
                solver.add(mkDistinct(dateValues.values().toArray(new Expr[0])));
            }
            Map<Timestamp, Expr> tsValues = valuesStack.stream().reduce(new HashMap<>(), (m, v) -> { m.putAll(v.tsValues); return m; }, (m1, m2) -> { m1.putAll(m2); return m1; });
            if (tsValues.size() > 1) {
                solver.add(mkDistinct(tsValues.values().toArray(new Expr[0])));
            }
            Map<Long, Expr> intValues = valuesStack.stream().reduce(new HashMap<>(), (m, v) -> { m.putAll(v.intValues); return m; }, (m1, m2) -> { m1.putAll(m2); return m1; });
            if (intValues.size() > 1) {
                solver.add(mkDistinct(intValues.values().toArray(new Expr[0])));
            }
            Map<Double, Expr> realValues = valuesStack.stream().reduce(new HashMap<>(), (m, v) -> { m.putAll(v.realValues); return m; }, (m1, m2) -> { m1.putAll(m2); return m1; });
            if (realValues.size() > 1) {
                solver.add(mkDistinct(realValues.values().toArray(new Expr[0])));
            }
            Map<String, Expr> stringValues = valuesStack.stream().reduce(new HashMap<>(), (m, v) -> { m.putAll(v.stringValues); return m; }, (m1, m2) -> { m1.putAll(m2); return m1; });
            if (stringValues.size() > 1) {
                solver.add(mkDistinct(stringValues.values().toArray(new Expr[0])));
            }
            return solver;
        }

        private String prepareSortDeclaration() {
            // Reusing prepareSolver is messy - some constants and sorts may not be used/declared.
            StringBuilder sb = new StringBuilder();
//            sb.append("(declare-sort ").append(dateSort.getSExpr()).append(" 0)\n");
//            sb.append("(declare-sort ").append(tsSort.getSExpr()).append(" 0)\n");
            sb.append("(declare-sort ").append(realSort.getSExpr()).append(" 0)\n");
            sb.append("(declare-sort ").append(stringSort.getSExpr()).append(" 0)\n");

            String customIntSortName = intSort.getSExpr();
            sb.append("(declare-sort ").append(customIntSortName).append(" 0)\n");
            sb.append(String.format("(declare-fun %s (%s %s) Bool)",
                    intLt.getSExpr(), customIntSortName, customIntSortName));

            prepareSortValues(sb, v -> v.dateValues);
            prepareSortValues(sb, v -> v.tsValues);
            prepareSortValues(sb, v -> v.intValues);
            prepareSortValues(sb, v -> v.realValues);
            prepareSortValues(sb, v -> v.stringValues);
            return sb.toString();
        }


        private <T> void prepareSortValues(StringBuilder sb, Function<Values, Map<T, Expr>> valueMapPicker) {
            Collection<Expr> values = valuesStack.stream().reduce(new HashSet<>(), (s, v) -> { s.addAll(valueMapPicker.apply(v).values()); return s; }, (s1, s2) -> { s1.addAll(s2); return s1; });
            StringBuilder distinct = new StringBuilder("(assert (distinct");
            for (Expr expr : values) {
                sb.append("(declare-fun ").append(expr.getSExpr()).append(" () ").append(expr.getSort().getSExpr()).append(")\n");
                distinct.append(' ').append(expr.getSExpr());
            }
            distinct.append("))\n");
            if (values.size() > 1) {
                sb.append(distinct);
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
        return super.mkAnd(boolExprs);
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

    public Expr mkCustomIntLt(Expr left, Expr right) { return customSorts.intLt.apply(left, right); }

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
