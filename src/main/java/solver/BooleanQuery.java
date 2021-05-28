package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;

import static com.google.common.base.Preconditions.checkArgument;

public abstract class BooleanQuery extends Query {
    protected abstract BoolExpr f(Instance instance);

    @Override
    public Sort[] headTypes() {
        return new Sort[0];
    }

    @Override
    public BoolExpr doesContain(Instance instance, Tuple tuple) {
        checkArgument(tuple.isEmpty());
        return f(instance);
    }
}
