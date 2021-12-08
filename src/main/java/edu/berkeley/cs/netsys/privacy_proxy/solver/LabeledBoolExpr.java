package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.BoolExpr;
import org.checkerframework.checker.nullness.qual.Nullable;

import java.util.stream.Collectors;

// A labeled conjunction of boolean expressions.
public class LabeledBoolExpr<L> {
    private final ImmutableList<BoolExpr> exprs; // Take conjunction of this.
    private final @Nullable L label;

    public LabeledBoolExpr(ImmutableList<BoolExpr> exprs, @Nullable L label) {
        this.exprs = exprs;
        this.label = label;
    }

    // For the named case, the expressions are labeled "label_i" for i=0,1,...
    public String makeAssertion() {
        if (label == null) {
            return exprs.stream().map(b -> "(assert " + b + ")").collect(Collectors.joining("\n"));
        }

        String labelString = label.toString();
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < exprs.size(); ++i) {
            sb.append(String.format("(assert (! %s :named %s_%d))\n", exprs.get(i), labelString, i));
        }
        return sb.toString();
    }

    public static <L> LabeledBoolExpr<L> makeUnlabeled(ImmutableList<BoolExpr> exprs) {
        return new LabeledBoolExpr<>(exprs, null);
    }

    public static <L> LabeledBoolExpr<L> makeUnlabeled(BoolExpr expr) {
        return makeUnlabeled(ImmutableList.of(expr));
    }

    public ImmutableList<BoolExpr> exprs() {
        return exprs;
    }

    public @Nullable L label() {
        return label;
    }
}
