package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import sql.QuerySequence;

import java.util.Collection;

public class BasicDeterminacyFormula extends DeterminacyFormula {
    public BasicDeterminacyFormula(Context context, Schema schema, Collection<Query> views) {
        super(context, schema, views);
    }

    @Override
    public BoolExpr makeFormula(QuerySequence queries) {
        Query query = queries.get(queries.size() - 1).query.getSolverQuery(schema);
        return context.mkAnd(
                context.mkNot(query.apply(context, inst1).equalsExpr(context, query.apply(context, inst2))),
                generateTupleCheck(queries),
                preparedExpr
        );
    }
}
