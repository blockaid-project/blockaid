package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;

public interface Function {
    BoolExpr apply(Expr... args);
}
