package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import static com.google.common.base.Preconditions.checkNotNull;

public abstract class Query {
    public abstract Sort[] headTypes();
    public abstract BoolExpr doesContain(Instance instance, Tuple tuple);
    public abstract Tuple[] generateTuples(Instance instance);
    public abstract BoolExpr[] generateExists(Instance instance);

    public Relation apply(Instance instance) {
        if (instance.isConcrete) {
            return new ConcreteRelation(instance.schema, headTypes(), generateTuples(instance), generateExists(instance));
        } else {
            return new GeneralRelation(instance.schema, (Expr... exprs) -> doesContain(instance, new Tuple(instance.schema, exprs)), headTypes());
        }
    }
}
