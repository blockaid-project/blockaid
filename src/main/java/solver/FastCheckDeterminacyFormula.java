package solver;

import com.microsoft.z3.BoolExpr;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class FastCheckDeterminacyFormula extends DeterminacyFormula{
    public FastCheckDeterminacyFormula(Schema schema, Collection<Query> views) {
        super(schema,
                (Integer instNum) -> schema.makeFreshInstance("instance" + instNum),
                (Instance inst1, Instance inst2) -> {
                    List<BoolExpr> clauses = new ArrayList<>();
                    clauses.addAll(inst1.getConstraints().values());
                    clauses.addAll(inst2.getConstraints().values());
                    for (Query v : views) {
                        clauses.add(v.apply(inst1).isContainedInExpr(v.apply(inst2)));
                    }
                    return clauses;
                });
    }
}
