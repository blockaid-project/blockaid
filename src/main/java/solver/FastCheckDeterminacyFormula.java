package solver;

import com.google.common.collect.Iterables;
import com.microsoft.z3.BoolExpr;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class FastCheckDeterminacyFormula extends DeterminacyFormula {
    public FastCheckDeterminacyFormula(Schema schema, Collection<Query> views, TextOption textOption) {
        super(schema,
                (Integer instNum) -> schema.makeFreshInstance("instance" + instNum),
                (Instance inst1, Instance inst2) -> {
                    List<BoolExpr> clauses = new ArrayList<>();
                    for (Iterable<BoolExpr> bs : inst1.getConstraints().values()) {
                        Iterables.addAll(clauses, bs);
                    }
                    for (Iterable<BoolExpr> bs : inst2.getConstraints().values()) {
                        Iterables.addAll(clauses, bs);
                    }
                    for (Query v : views) {
                        Iterables.addAll(clauses, v.apply(inst1).isContainedInExpr(v.apply(inst2)));
                    }
                    return clauses;
                }, textOption);
    }

    public FastCheckDeterminacyFormula(Schema schema, Collection<Query> views) {
        this(schema, views, TextOption.USE_TEXT);
    }
}
