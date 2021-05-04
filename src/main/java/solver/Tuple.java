package solver;

import com.microsoft.z3.*;

import java.text.ParseException;
import java.text.SimpleDateFormat;
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
        if (isEmpty()) {
            return context.mkTrue();
        }

        BoolExpr[] exprs = new BoolExpr[size()];
        for (int i = 0; i < size(); ++i) {
            exprs[i] = context.mkEq(get(i), other.get(i));
        }
        return context.mkAnd(exprs);
    }

    public static Sort getSortFromObject(Context context, Object value) {
        if (value instanceof Integer || value instanceof Long || value instanceof Boolean) {
            return context.getIntSort();
        } else if (value instanceof Double) {
            return context.getRealSort();
        } else if (value instanceof String) {
            try {
                new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").parse((String) value);
                return context.getIntSort();
            } catch (ParseException e) {
                // do nothing
            }
            return context.getStringSort();
        } else if (value instanceof Expr) {
            return ((Expr) value).getSort();
        } else if (value == null) {
            throw new UnsupportedOperationException("null value unhandled");
        } else {
            throw new UnsupportedOperationException("unknown type for constant loading");
        }
    }

    public static Expr getExprFromObject(Context context, Object value) {
        if (value instanceof Integer) {
            return context.mkInt((Integer) value);
        } else if (value instanceof Long) {
            return context.mkInt((Long) value);
        } else if (value instanceof Boolean) {
            // TODO(zhangwen): "casting" boolean into int.
            return ((Boolean) value) ? context.mkInt(1) : context.mkInt(0);
        } else if (value instanceof Double) {
            throw new UnsupportedOperationException("float loading todo");
        } else if (value instanceof String) {
            try {
                return context.mkInt(new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").parse((String) value).getTime());
            } catch (ParseException e) {
                // do nothing
            }
            return context.mkString((String) value);
        } else if (value instanceof Expr) {
            return (Expr) value;
        } else if (value == null) {
            // FIXME(zhangwen): handle NULL properly.
            return null;
        } else {
            throw new UnsupportedOperationException("unknown type for constant loading: " + value);
        }
    }
}
