package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

public class Tuple extends ArrayList<Expr> {
    public Tuple(int i) {
        super(i);
    }

    public Tuple() {
        super();
    }

    public Tuple(Collection<? extends Expr> collection) {
        super(collection);
    }

    public Tuple(Expr... exprs) {
        super(Arrays.asList(exprs));
    }

    BoolExpr tupleEqual(Context context, Tuple other) {
        assert size() == other.size();

        BoolExpr[] exprs = new BoolExpr[size()];
        for (int i = 0; i < size(); ++i) {
            exprs[i] = context.mkEq(get(i), other.get(i));
        }
        return context.mkAnd(exprs);
    }

    public static Expr getExprFromObject(Context context, Object value) {
        if (value instanceof Integer) {
            return context.mkInt((Integer) value);
        } else if (value instanceof Double) {
            throw new UnsupportedOperationException("float loading todo");
        } else if (value instanceof String) {
            return context.mkString((String) value);
        } else if (value == null) {
            throw new UnsupportedOperationException("null value unhandled");
        } else {
            throw new UnsupportedOperationException("unknown type for constant loading");
        }
    }
}
