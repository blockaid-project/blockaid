package solver;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.*;
import solver.context.MyZ3Context;

import java.sql.Date;
import java.sql.Timestamp;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class Tuple {
    private final Schema schema;
    private final ImmutableList<Optional<Expr>> content; // empty denotes null.

    public Tuple(Schema schema, Expr... exprs) {
        this(schema, Arrays.stream(exprs));
    }

    public Tuple(Schema schema, Stream<Expr> exprs) {
        this.content = exprs.map(Optional::ofNullable).collect(ImmutableList.toImmutableList());
        this.schema = checkNotNull(schema);
    }

    public Schema getSchema() {
        return schema;
    }

    public int size() {
        return content.size();
    }

    public boolean isEmpty() {
        return content.isEmpty();
    }

    public Expr get(int i) {
        return content.get(i).orElse(null);
    }

    public Stream<Expr> stream() {
        return content.stream().map(v -> v.orElse(null));
    }

    BoolExpr equalsExpr(Tuple other) {
        checkArgument(getSchema() == other.getSchema(), "tuple schemas differ");
        checkArgument(size() == other.size(),
                "tuple sizes are different: %s vs %s", size(), other.size());

        MyZ3Context context = schema.getContext();
        if (isEmpty()) {
            return context.mkTrue();
        }

        BoolExpr[] exprs = new BoolExpr[size()];
        for (int i = 0; i < size(); ++i) {
            Expr lhs = get(i), rhs = other.get(i);
            Optional<Object> lhsV = context.getValueForExpr(lhs), rhsV = context.getValueForExpr(rhs);
            if (lhsV.isPresent() && rhsV.isPresent() && !lhsV.get().equals(rhsV.get())) {
                // LHS and RHS represent distinct concrete values, which can't be equal!
                return context.mkFalse();
            }
            exprs[i] = context.mkEq(get(i), other.get(i));
        }
        return context.mkAnd(exprs);
    }

    public List<Expr> toExprList() {
        return stream().collect(Collectors.toList());
    }

    public Expr[] toExprArray() {
        return stream().toArray(Expr[]::new);
    }

    /**
     * Returns a tuple with NULL elements replaced with fresh constants.
     * @param sorts the sorts of tuple elements; provides the sorts for NULLs.
     * @return a tuple with NULLs replaced replaced.
     */
    public Tuple replaceNullsWithFreshConsts(Sort[] sorts) {
        // FIXME(zhangwen): handle SQL NULL properly.
        // Here I'm using a fresh symbol for NULL.  Assuming that we see NULL here only when a previous query returned
        // NULL, this is... safe?  At least not blatantly unsafe.  I need to think through this...
        checkArgument(sorts.length == size());
        if (content.stream().noneMatch(Optional::isEmpty)) {
            return this;
        }

        Expr[] convertedExprs = new Expr[size()];
        for (int i = 0; i < size(); ++i) {
            convertedExprs[i] = content.get(i).orElse(schema.getContext().mkFreshConst("null", sorts[i]));
//            convertedExprs[i] = content.get(i).orElse(schema.getContext().mkConst("null" + sorts[i].toString(), sorts[i]));
        }

        return new Tuple(this.getSchema(), convertedExprs);
    }

    @Override
    public String toString() {
        return "Tuple{" +
                "content=" + content +
                '}';
    }

    // FIXME(zhangwen): move to MyZ3Context?
    public static Sort getSortFromObject(MyZ3Context context, Object value) {
        if (value instanceof Integer || value instanceof Long) {
            return context.getCustomIntSort();
        } else if (value instanceof Boolean) {
            return context.getCustomBoolSort();
        } else if (value instanceof Double) {
            return context.getCustomRealSort();
        } else if (value instanceof String) {
            return context.getCustomStringSort();
        } else if (value instanceof Date) {
            return context.getDateSort();
        } else if (value instanceof Timestamp) {
            return context.getTimestampSort();
        } else if (value instanceof Expr) {
            return ((Expr) value).getSort();
        } else if (value == null) {
            throw new UnsupportedOperationException("null value unhandled");
        } else {
            throw new UnsupportedOperationException("unknown type for constant loading");
        }
    }

    public static Expr getExprFromObject(MyZ3Context context, Object value) {
        if (value instanceof Integer i) {
            return context.mkCustomInt(i);
        } else if (value instanceof Long l) {
            return context.mkCustomInt(l);
        } else if (value instanceof Boolean b) {
            return context.mkCustomBool(b);
        } else if (value instanceof Double d) {
            return context.mkCustomReal(d);
        } else if (value instanceof String s) {
            return context.mkCustomString(s);
        } else if (value instanceof Date d) {
            return context.mkDate(d);
        } else if (value instanceof Timestamp ts) {
            return context.mkTimestamp(ts);
        } else if (value instanceof Expr) {
            return (Expr) value;
        } else if (value == null) {
            // FIXME(zhangwen): handle NULL properly.
            return null;
        } else {
            throw new UnsupportedOperationException("unknown type for constant loading: " + value);
        }
    }

    // FIXME(zhangwen): move this somewhere.
    public static boolean valueLessThan(Object value1, Object value2) {
        if (value1 instanceof Integer) {
            value1 = Long.valueOf((Integer) value1);
        }
        if (value2 instanceof Integer) {
            value2 = Long.valueOf((Integer) value2);
        }
        if (value1 instanceof Long && value2 instanceof Long && (long) value1 < (long) value2) {
            return true;
        }
        if (value1 instanceof Timestamp && value2 instanceof Timestamp
                && ((Timestamp) value1).compareTo((Timestamp) value2) < 0) {
            return true;
        }
        if (value1 instanceof Date && value2 instanceof Date && ((Date) value1).compareTo((Date) value2) < 0) {
            return true;
        }
        return false;
    }

    // For decision template generation / matching.
    public static Object normalizeValue(Object v) {
        return v;
//        if (v instanceof Boolean) {
//            return ((boolean) v) ? 1 : 0;
//        }
//        return v;
    }
}
