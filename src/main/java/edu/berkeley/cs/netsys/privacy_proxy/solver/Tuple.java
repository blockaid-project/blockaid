package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.sql.Date;
import java.sql.Timestamp;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class Tuple<C extends Z3ContextWrapper<?, ?, ?, ?>> {
    private final Schema<C> schema;
    private final ImmutableList<Optional<Expr<?>>> content; // empty denotes null.

    public Tuple(Schema<C> schema, Expr<?>... exprs) {
        this(schema, Arrays.stream(exprs));
    }

    public Tuple(Schema<C> schema, Collection<Expr<?>> exprs) {
        this(schema, exprs.stream());
    }

    public Tuple(Schema<C> schema, Stream<Expr<?>> exprs) {
        ImmutableList.Builder<Optional<Expr<?>>> builder = new ImmutableList.Builder<>();
        exprs.forEach(e -> builder.add(Optional.ofNullable(e)));
        this.content = builder.build();
        this.schema = checkNotNull(schema);
    }

    public Schema<C> getSchema() {
        return schema;
    }

    public int size() {
        return content.size();
    }

    public boolean isEmpty() {
        return content.isEmpty();
    }

    public Expr<?> get(int i) {
        return content.get(i).orElse(null);
    }

    public Stream<Expr<?>> stream() {
        return content.stream().map(v -> v.orElse(null));
    }

    BoolExpr equalsExpr(Tuple<C> other) {
        checkArgument(getSchema() == other.getSchema(), "tuple schemas differ");
        checkArgument(size() == other.size(),
                "tuple sizes are different: %s vs %s", size(), other.size());

        C context = schema.getContext();
        if (isEmpty()) {
            return context.mkTrue();
        }

        ArrayList<BoolExpr> exprs = new ArrayList<>();
        for (int i = 0; i < size(); ++i) {
            Expr<?> lhs = get(i), rhs = other.get(i);
            if (context.areDistinctConstants(lhs, rhs)) {
                // LHS and RHS represent distinct concrete values, which can't be equal!
                return context.mkFalse();
            }
            exprs.add(context.mkIsSameValue(get(i), other.get(i)));
        }
        return context.mkAnd(exprs);
    }

    public List<Expr<?>> toExprList() {
        return stream().collect(Collectors.toList());
    }

    public Expr<?>[] toExprArray() {
        return stream().toArray(Expr[]::new);
    }

    /**
     * Returns a tuple with NULL elements replaced with actual null values.
     * TODO(zhangwen): make null exprs when tuples are made, instead of replacing them after the fact?
     * @param sorts the sorts of tuple elements; provides the sorts for NULLs.
     * @return a tuple with NULLs replaced.
     */
    public Tuple<C> fillNulls(List<Sort> sorts) {
        checkArgument(sorts.size() == size());
        if (content.stream().noneMatch(Optional::isEmpty)) {
            return this;
        }

        Expr<?>[] convertedExprs = new Expr[size()];
        for (int i = 0; i < size(); ++i) {
            Sort thisSort = sorts.get(i);
            convertedExprs[i] = content.get(i).orElseGet(() -> schema.getContext().mkNull(thisSort));
        }

        return new Tuple<>(this.getSchema(), convertedExprs);
    }

    @Override
    public String toString() {
        return "Tuple{" +
                "content=" + content +
                '}';
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
}
