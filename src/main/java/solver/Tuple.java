package solver;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.*;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class Tuple {
    private final Schema schema;
    private final List<Expr> content; // Can't use `ImmutableList` because a `Tuple` can contain nulls.

    public Tuple(Schema schema, Expr... exprs) {
        // FIXME(zhangwen): `List.of` doesn't allow nulls, but we do?
        this.content = List.of(exprs);
        this.schema = schema;
    }

    public Tuple(Schema schema, Stream<Expr> exprs) {
        // The "fused" version doesn't allow nulls in the list.
        //noinspection FuseStreamOperations
        List<Expr> exprList = exprs.collect(Collectors.toList());
        this.content = Collections.unmodifiableList(exprList);
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
        return content.get(i);
    }

    public Stream<Expr> stream() {
        return content.stream();
    }

    public List<Expr> content() {
        return content;
    }

    BoolExpr tupleEqual(Tuple other) {
        checkArgument(getSchema() == other.getSchema(), "tuple schemas differ");
        checkArgument(size() == other.size(),
                "tuple sizes are different: %s vs %s", size(), other.size());

        Context context = schema.getContext();
        if (isEmpty()) {
            return context.mkTrue();
        }

        BoolExpr[] exprs = new BoolExpr[size()];
        for (int i = 0; i < size(); ++i) {
            exprs[i] = context.mkEq(get(i), other.get(i));
        }
        return context.mkAnd(exprs);
    }

    public Expr[] toExprArray() {
        return content.toArray(new Expr[0]);
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
