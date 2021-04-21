package solver;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import java.util.HashSet;

public class MyZ3Context extends Context {
    public MyZ3Context() {
        super();
        isTrackingConsts = false;
        consts = new HashSet<>();
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

    private boolean isTrackingConsts;
    private final HashSet<Expr> consts;
}
