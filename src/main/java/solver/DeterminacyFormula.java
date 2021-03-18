package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import sql.QuerySequence;
import sql.QueryWithResult;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
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

        List<BoolExpr> clauses = new ArrayList<>();
        if (inst1.constraint != null) {
            clauses.add(inst1.constraint);
        }
        if (inst2.constraint != null) {
            clauses.add(inst2.constraint);
        }
        for (Query v : views) {
            clauses.add(v.apply(context, inst1).isContainedIn(context, v.apply(context, inst2)));
        }
        this.preparedExpr = context.mkAnd(clauses.toArray(new BoolExpr[0]));
    }

    public abstract BoolExpr makeFormula(QuerySequence queries);

    protected BoolExpr generateTupleCheck(QuerySequence queries) {
        List<BoolExpr> exprs = new ArrayList<>();
        for (QueryWithResult queryWithResult : queries) {
            Query query = queryWithResult.query.getSolverQuery(schema);
            Relation r1 = query.apply(context, inst1);
            Relation r2 = query.apply(context, inst2);
            if (queryWithResult.tuples != null) {
                List<Tuple> tuples = queryWithResult.tuples.stream().map(tuple -> new Tuple(tuple.stream().map(v -> Tuple.getExprFromObject(context, v)).toArray(Expr[]::new))).collect(Collectors.toList());
                exprs.add(r1.doesContain(context, tuples));
                exprs.add(r2.doesContain(context, tuples));
            }
        }
        return context.mkAnd(exprs.toArray(new BoolExpr[0]));
    }
}
