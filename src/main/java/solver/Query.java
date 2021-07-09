package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import java.util.Arrays;
import java.util.Collections;

public abstract class Query {
    public abstract Schema getSchema();
    public abstract Sort[] headTypes();
    public abstract BoolExpr doesContain(Instance instance, Tuple tuple);
    public abstract Tuple[] generateTuples(Instance instance);
    public abstract BoolExpr[] generateExists(Instance instance);

    public Iterable<Query> getComponents() {
        return Collections.singletonList(this);
    }

    public Relation apply(Instance instance) {
        if (instance.isConcrete) {
            return new ConcreteRelation(instance.schema, headTypes(), generateTuples(instance), generateExists(instance));
        } else {
            return new GeneralRelation(instance.schema, (Expr... exprs) -> doesContain(instance, new Tuple(instance.schema, exprs)), headTypes());
        }
    }

    public Tuple makeFreshHead() {
        Schema schema = getSchema();
        MyZ3Context context = schema.getContext();
        return new Tuple(getSchema(), Arrays.stream(headTypes()).map(t -> context.mkFreshConst("z", t)));
    }
}
