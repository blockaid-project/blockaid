package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.BoolExpr;
import org.checkerframework.checker.nullness.qual.Nullable;

// TODO(zhangwen): take list of `BoolExpr`s?
class NamedBoolExpr extends LabeledBoolExpr<String> {
    public NamedBoolExpr(Iterable<BoolExpr> exprs, @Nullable String name) {
        super(ImmutableList.copyOf(exprs), name);
    }

    public String name() {
        return label();
    }

    public static NamedBoolExpr makeUnnamed(Iterable<BoolExpr> exprs) {
        return new NamedBoolExpr(exprs, null);
    }

    public static NamedBoolExpr makeUnnamed(BoolExpr expr) {
        return makeUnnamed(ImmutableList.of(expr));
    }
}
