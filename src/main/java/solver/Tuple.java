package solver;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.*;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Collections;
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
        }

        return new Tuple(this.getSchema(), convertedExprs);
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
