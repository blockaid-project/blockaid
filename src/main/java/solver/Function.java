package solver;

import com.microsoft.z3.Expr;

public interface Function {
    Expr apply(Expr... args);
}
