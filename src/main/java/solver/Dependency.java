package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

public interface Dependency {
    BoolExpr apply(Instance instance);
}
