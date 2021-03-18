package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;

public class UnionQuery<QT> extends Query {
    public Query[] queries;
    private Sort[] headTypes;

    public UnionQuery(Query... queries) {
        super();

        assert queries.length > 0;

        this.queries = queries;
        this.headTypes = this.queries[0].headTypes();
    }

    @Override
    public Sort[] headTypes() {
        return headTypes;
    }

    @Override
    public BoolExpr doesContain(Context context, Instance instance, Tuple tuple) {
        BoolExpr[] exprs = new BoolExpr[queries.length];
        for (int i = 0; i < queries.length; ++i) {
            exprs[i] = queries[i].doesContain(context, instance, tuple);
        }
        return context.mkOr(exprs);
    }
}
