package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Sort;

import java.util.Arrays;

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
    public BoolExpr doesContain(Instance instance, Tuple tuple) {
        BoolExpr[] exprs = new BoolExpr[queries.length];
        for (int i = 0; i < queries.length; ++i) {
            exprs[i] = queries[i].doesContain(instance, tuple);
        }
        return instance.getContext().mkOr(exprs);
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
