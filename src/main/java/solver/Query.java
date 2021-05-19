package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

public abstract class Query {
    public abstract Sort[] headTypes();
    public abstract BoolExpr doesContain(Instance instance, Tuple tuple);

    public Relation apply(Instance instance) {
        return new Relation(instance.schema, (Expr... exprs) -> doesContain(instance, new Tuple(instance.schema, exprs)), headTypes());
    }
}
