package solver;

import cache.QueryTrace;
import com.microsoft.z3.BoolExpr;

import java.util.*;
import java.util.function.Function;

public class BoundedDeterminacyFormula extends DeterminacyFormula {
    private static Function<Integer, Instance> getInstanceMaker(Schema schema, BoundEstimator bounds, QueryTrace queries) {
        final Map<String, Integer> calculatedBounds = bounds.calculateBounds(schema, queries);
        return (Integer instNum) -> schema.makeConcreteInstance("instance" + instNum, calculatedBounds);
    }

    public BoundedDeterminacyFormula(Schema schema, Collection<Query> views, BoundEstimator bounds, QueryTrace queries) {
        super(schema, getInstanceMaker(schema, bounds, queries), (Instance inst1, Instance inst2) -> {
            List<BoolExpr> clauses = new ArrayList<>();
            clauses.addAll(inst1.getConstraints().values());
            clauses.addAll(inst2.getConstraints().values());
            for (Query v : views) {
                clauses.add(v.apply(inst1).equalsExpr(v.apply(inst2)));
            }
            return clauses;
        });
    }
}
