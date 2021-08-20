package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import java.util.Arrays;
import java.util.Collections;
import java.util.function.IntFunction;

public abstract class Query {
    public abstract Schema getSchema();
    public abstract Sort[] headTypes();
    public abstract BoolExpr doesContain(Instance instance, Tuple tuple);
    public abstract Tuple[] generateTuples(Instance instance);
    public abstract BoolExpr[] generateExists(Instance instance);

    /**
     * Returns a set of queries which, when joined together by cartesian product,
     * yields a query equivalent to the original query. Used to optimize bounded formula
     * generation for policies with cartesian products.
     */
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

    public Tuple makeHead(IntFunction<String> nameGenerator) {
        Schema schema = getSchema();
        MyZ3Context context = schema.getContext();

        Sort[] sorts = this.headTypes();
        int numColumns = sorts.length;
        Expr[] head = new Expr[numColumns];
        for (int i = 0; i < numColumns; ++i) {
            head[i] = context.mkConst(nameGenerator.apply(i), sorts[i]);
        }
        return new Tuple(schema, head);
    }

    public Tuple makeFreshHead() {
        Schema schema = getSchema();
        MyZ3Context context = schema.getContext();
        return new Tuple(schema, Arrays.stream(headTypes()).map(t -> context.mkFreshConst("z", t)));
    }
}
