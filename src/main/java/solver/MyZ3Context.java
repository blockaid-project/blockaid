package solver;

import com.microsoft.z3.*;

import java.sql.Date;
import java.sql.Timestamp;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

public class MyZ3Context extends Context {
    private boolean isTrackingConsts;
    private final HashSet<Expr> consts;

    private final Sort dateSort;
    private final Map<Date, Expr> dateValues;
    private final Sort tsSort;
    private final Map<Timestamp, Expr> tsValues;
    private final Sort intSort;
    private final Map<Long, Expr> intValues;
    private final Sort realSort;
    private final Map<Double, Expr> realValues;
    private final Sort stringSort;
    private final Map<String, Expr> stringValues;

    public MyZ3Context() {
        super();
        isTrackingConsts = false;
        consts = new HashSet<>();
        dateSort = this.mkUninterpretedSort("DATE");
        dateValues = new HashMap<>();
        tsSort = this.mkUninterpretedSort("TS");
        tsValues = new HashMap<>();
        intSort = this.mkUninterpretedSort("INT");
        intValues = new HashMap<>();
        realSort = this.mkUninterpretedSort("REAL");
        realValues = new HashMap<>();
        stringSort = this.mkUninterpretedSort("STRING");
        stringValues = new HashMap<>();
    }

    @Override
    public Expr mkConst(String s, Sort sort) {
        Expr c = super.mkConst(s, sort);
        if (isTrackingConsts) {
            consts.add(c);
        }
        return c;
    }

    @Override
    public Expr mkFreshConst(String s, Sort sort) {
        Expr c = super.mkFreshConst(s, sort);
        if (isTrackingConsts) {
            consts.add(c);
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
        consts.clear();
        isTrackingConsts = true;
    }

    public void stopTrackingConsts() {
        isTrackingConsts = false;
    }

    public Iterable<Expr> getConsts() {
        return consts;
    }

    @Override
    public Solver mkSolver() {
        return prepareSolver(super.mkSolver());
    }

    @Override
    public Solver mkSolver(Symbol symbol) {
        return prepareSolver(super.mkSolver(symbol));
    }

    @Override
    public Solver mkSolver(String s) {
        return prepareSolver(super.mkSolver(s));
    }

    @Override
    public Solver mkSimpleSolver() {
        return prepareSolver(super.mkSimpleSolver());
    }

    @Override
    public Solver mkSolver(Tactic tactic) {
        return prepareSolver(super.mkSolver(tactic));
    }

    private Solver prepareSolver(Solver solver) {
        if (!tsValues.isEmpty()) {
            solver.add(mkDistinct(tsValues.values().toArray(new Expr[0])));
        }
        if (!dateValues.isEmpty()) {
            solver.add(mkDistinct(dateValues.values().toArray(new Expr[0])));
        }
        if (!intValues.isEmpty()) {
            solver.add(mkDistinct(intValues.values().toArray(new Expr[0])));
        }
        if (!realValues.isEmpty()) {
            solver.add(mkDistinct(realValues.values().toArray(new Expr[0])));
        }
        if (!stringValues.isEmpty()) {
            solver.add(mkDistinct(stringValues.values().toArray(new Expr[0])));
        }
        return solver;
    }

    public Sort getDateSort() {
        return dateSort;
    }

    public Expr mkDate(Date date) {
        return dateValues.computeIfAbsent(date, k -> mkFreshConst("DATE", dateSort));
    }

    public Sort getTimestampSort() {
        return tsSort;
    }

    public Expr mkTimestamp(Timestamp ts) {
        return tsValues.computeIfAbsent(ts, k -> mkFreshConst("TS", tsSort));
    }

    public Sort getCustomIntSort() {
        return intSort;
    }

    public Expr mkCustomInt(long value) {
        return intValues.computeIfAbsent(value, k -> mkFreshConst("INT", intSort));
    }

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
        return realSort;
    }

    public Expr mkCustomReal(double value) {
        return realValues.computeIfAbsent(value, k -> mkFreshConst("REAL", intSort));
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
        return stringSort;
    }

    public Expr mkCustomString(String value) {
        return stringValues.computeIfAbsent(value, k -> mkFreshConst("STRING", stringSort));
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
