package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.StringSymbol;
import sql.QuerySequence;
import sql.QueryWithResult;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public abstract class DeterminacyFormula {
    protected Context context;
    protected Schema schema;
    protected Instance inst1;
    protected Instance inst2;
    protected BoolExpr preparedExpr;

    protected DeterminacyFormula(Context context, Schema schema, Collection<Query> views) {
        this.context = context;
        this.schema = schema;
        this.inst1 = schema.makeFreshInstance(context);
        this.inst2 = schema.makeFreshInstance(context);
    }

    public abstract BoolExpr makeFormula(QuerySequence queries);

    protected BoolExpr generateTraceConformanceExpr(QuerySequence queries) {
        List<BoolExpr> exprs = new ArrayList<>();

        // `inst1` and `inst2` must be consistent with the results of previous queries.
        for (QueryWithResult queryWithResult : queries.getTrace()) {
            Query query = queryWithResult.query.getSolverQuery(schema);
            Relation r1 = query.apply(context, inst1);
            Relation r2 = query.apply(context, inst2);
            if (queryWithResult.tuples != null) {
                List<Tuple> tuples = queryWithResult.tuples.stream().map(tuple -> new Tuple(tuple.stream().map(v -> Tuple.getExprFromObject(context, v)).toArray(Expr[]::new))).collect(Collectors.toList());
                exprs.add(r1.doesContain(context, tuples));
                exprs.add(r2.doesContain(context, tuples));
            }
        }

        // Constrain constant values.
        for (Map.Entry<String, Integer> entry : queries.getConstMap().entrySet()) {
            StringSymbol nameSymbol = context.mkSymbol("@" + entry.getKey());
            exprs.add(context.mkEq(
                    context.mkConst(nameSymbol, context.getIntSort()),
                    context.mkInt(entry.getValue())
            ));
        }

        return context.mkAnd(exprs.toArray(new BoolExpr[0]));
    }
}
