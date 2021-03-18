package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;


public interface Constraint {
    BoolExpr apply(Context context, Expr column);
}
