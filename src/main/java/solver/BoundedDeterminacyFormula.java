package solver;

import com.microsoft.z3.BoolExpr;

import java.util.*;

public class BoundedDeterminacyFormula extends DeterminacyFormula {
    public BoundedDeterminacyFormula(Schema schema, Collection<Query> views, Map<String, Integer> bounds) {
        super(schema, (Integer instNum) -> schema.makeConcreteInstance("instance" + instNum, bounds), (Instance inst1, Instance inst2) -> {
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
