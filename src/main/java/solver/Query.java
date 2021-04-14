package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

public abstract class Query {
    public abstract Sort[] headTypes();
    public abstract BoolExpr doesContain(Context context, Instance instance, Tuple tuple);

    public Relation apply(Context context, Instance instance) {
        return new Relation(context, (Expr... exprs) -> doesContain(context, instance, new Tuple(exprs)), headTypes());
    }
}
