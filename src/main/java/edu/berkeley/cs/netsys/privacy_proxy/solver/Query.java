package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.function.IntFunction;

public abstract class Query<C extends Z3ContextWrapper<?, ?, ?, ?>> {
    public abstract Schema<C> getSchema();
    public abstract Sort[] headTypes();
    // To generate expression for "Q(inst) contains tup", use `query.apply(inst).doesContainExpr(tup)`.
    protected abstract Iterable<BoolExpr> doesContain(Instance<C> instance, Tuple<C> tuple);
    protected abstract List<Tuple<C>> generateTuples(Instance<C> instance);
    protected abstract List<BoolExpr> generateExists(Instance<C> instance);

    /**
     * Returns a set of queries which, when joined together by cartesian product,
     * yields a query equivalent to the original query. Used to optimize bounded formula
     * generation for policies with cartesian products.
     */
    public Iterable<Query<C>> getComponents() {
        return Collections.singletonList(this);
    }

    public Relation<C> apply(Instance<C> instance) {
        Schema<C> schema = instance.getSchema();
        if (instance.isBounded()) {
            return new ConcreteRelation<>(schema, headTypes(), generateTuples(instance), generateExists(instance));
        } else {
            return new GeneralRelation<>(schema, (Expr<?>... exprs) -> doesContain(instance, new Tuple<>(schema, exprs)), headTypes());
        }
    }

    public Tuple<C> makeHead(IntFunction<String> nameGenerator) {
        Schema<C> schema = getSchema();
        C context = schema.getContext();

        Sort[] sorts = this.headTypes();
        int numColumns = sorts.length;

        ArrayList<Expr<?>> head = new ArrayList<>();
        for (int i = 0; i < numColumns; ++i) {
            head.add(context.mkConst(nameGenerator.apply(i), sorts[i]));
        }
        return new Tuple<>(schema, head);
    }

    public Tuple<C> makeFreshHead() {
        Schema<C> schema = getSchema();
        C context = schema.getContext();
        return new Tuple<>(schema, Arrays.stream(headTypes()).map(t -> context.mkFreshConst("z", t)));
    }

    public Tuple<C> makeFreshExistentialHead() {
        Schema<C> schema = getSchema();
        C context = schema.getContext();
        return new Tuple<>(schema, Arrays.stream(headTypes()).map(t -> context.mkFreshQuantifiedConst("e", t)));
    }
}
