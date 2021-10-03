package solver;

import com.microsoft.z3.BoolExpr;
import org.checkerframework.checker.nullness.qual.Nullable;

record NamedBoolExpr(BoolExpr expr, @Nullable String name) {
    public static NamedBoolExpr makeUnnamed(BoolExpr expr) {
        return new NamedBoolExpr(expr, null);
    }

    public String makeAssertion() {
        if (name == null) {
            return "(assert " + expr + ")";
        }
        return "(assert (! " + expr + " :named " + name + "))";
    }
}
