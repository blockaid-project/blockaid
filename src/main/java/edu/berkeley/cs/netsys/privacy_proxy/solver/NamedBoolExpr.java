package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.BoolExpr;
import org.checkerframework.checker.nullness.qual.Nullable;

// TODO(zhangwen): take list of `BoolExpr`s?
class NamedBoolExpr extends LabeledBoolExpr<String> {
    public NamedBoolExpr(BoolExpr expr, @Nullable String name) {
        super(expr, name);
    }

    public String name() {
        return label();
    }

    public static NamedBoolExpr makeUnnamed(BoolExpr expr) {
        return new NamedBoolExpr(expr, null);
    }
}
