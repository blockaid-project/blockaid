package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;

import static com.google.common.base.Preconditions.checkArgument;

public class UnionQuery extends Query {
    public final Query[] queries;
    private final Sort[] headTypes;

    public UnionQuery(Query... queries) {
        super();

        checkArgument(queries.length > 0);

        this.queries = queries;
        this.headTypes = this.queries[0].headTypes();
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
}
