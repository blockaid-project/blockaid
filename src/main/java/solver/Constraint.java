package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

import java.util.List;

public interface Constraint {
    BoolExpr apply(Instance instance);
    List<String> getRelevantColumns();
}
