package solver;

import cache.QueryTrace;
import com.microsoft.z3.BoolExpr;

import java.util.*;

public class BoundedDeterminacyFormula extends DeterminacyFormula {
    // TODO this
    private static Map<String, Integer> makeBoundsMap(Schema schema) {
        Map<String, Integer> m = new HashMap<>();
        for (String relationName : schema.getRelationNames()) {
            m.put(relationName, 2);
        }
        return m;
    }

    public BoundedDeterminacyFormula(Schema schema, Collection<Query> views) {
        super(schema, (Integer instNum) -> schema.makeConcreteInstance("instance" + instNum, makeBoundsMap(schema)), (Instance inst1, Instance inst2) -> {
            List<BoolExpr> clauses = new ArrayList<>();
            clauses.addAll(inst1.constraints);
            clauses.addAll(inst2.constraints);
            for (Query v : views) {
                clauses.add(v.apply(inst1).equalsExpr(v.apply(inst2)));
            }
            return clauses;
        });
    }

    @Override
    public BoolExpr makeFormula(QueryTrace queries) {
        Query query = queries.getCurrentQuery().getQuery().getSolverQuery(schema);
        return context.mkAnd(
                context.mkNot(query.apply(inst1).equalsExpr(query.apply(inst2))),
                generateTupleCheck(queries)
        );
    }
}
