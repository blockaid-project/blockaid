package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.BoolExpr;
import org.checkerframework.checker.nullness.qual.Nullable;

public class LabeledBoolExpr<L> {
    private final BoolExpr expr;
    private final @Nullable L label;

    public LabeledBoolExpr(BoolExpr expr, @Nullable L label) {
        this.expr = expr;
        this.label = label;
    }

    public String makeAssertion() {
        if (label == null) {
            return "(assert " + expr + ")";
        }
        return "(assert (! " + expr + " :named " + label + "))";
    }

    public static <L> LabeledBoolExpr<L> makeUnlabeled(BoolExpr expr) {
        return new LabeledBoolExpr<>(expr, null);
    }

    public BoolExpr expr() {
        return expr;
    }

    public @Nullable L label() {
        return label;
    }
}
