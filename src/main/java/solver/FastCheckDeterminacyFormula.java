package solver;

import cache.QueryTrace;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class FastCheckDeterminacyFormula extends DeterminacyFormula{
    public FastCheckDeterminacyFormula(Schema schema, Collection<Query> views) {
        super(schema, (Integer instNum) -> schema.makeFreshInstance(), (Instance inst1, Instance inst2) -> {
            List<BoolExpr> clauses = new ArrayList<>();
            clauses.addAll(inst1.constraints);
            clauses.addAll(inst2.constraints);
            for (Query v : views) {
                clauses.add(v.apply(inst1).isContainedIn(v.apply(inst2)));
            }
            return clauses;
        });
    }

    @Override
    public BoolExpr makeFormula(QueryTrace queries) {
        Query query = queries.getCurrentQuery().getQuery().getSolverQuery(schema);
        Tuple extHeadTup = query.makeFreshHead();
        return context.mkAnd(
                query.doesContain(inst1, extHeadTup),
                context.mkNot(query.doesContain(inst2, extHeadTup)),
                generateTupleCheck(queries)
        );
    }
}
