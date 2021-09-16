package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Sort;
import solver.context.MyZ3Context;

import java.util.Arrays;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;

public class UnionQuery extends Query {
    public final Query[] queries;
    private final Sort[] headTypes;

    public UnionQuery(Query... queries) {
        super();

        checkArgument(queries.length > 0);
        for (int i = 1; i < queries.length; ++i) {
            checkArgument(queries[i].getSchema() == queries[0].getSchema());
        }

        this.queries = queries;
        this.headTypes = this.queries[0].headTypes();
    }

    @Override
    public Schema getSchema() {
        return queries[0].getSchema();
    }

    @Override
    public Sort[] headTypes() {
        return headTypes;
    }

    @Override
    public Iterable<BoolExpr> doesContain(Instance instance, Tuple tuple) {
        MyZ3Context context = instance.getContext();
        BoolExpr[] exprs = new BoolExpr[queries.length];
        for (int i = 0; i < queries.length; ++i) {
            exprs[i] = context.mkAnd(queries[i].doesContain(instance, tuple));
        }
        return List.of(context.mkOr(exprs));
    }

    @Override
    public Tuple[] generateTuples(Instance instance) {
        return Arrays.stream(queries).map(q -> q.generateTuples(instance)).flatMap(Arrays::stream).toArray(Tuple[]::new);
    }

    @Override
    public BoolExpr[] generateExists(Instance instance) {
        return Arrays.stream(queries).map(q -> q.generateExists(instance)).flatMap(Arrays::stream).toArray(BoolExpr[]::new);
    }
}
