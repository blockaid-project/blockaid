package solver;

import com.microsoft.z3.BoolExpr;

import java.util.*;

public class BoundedDeterminacyFormula extends DeterminacyFormula {
    public BoundedDeterminacyFormula(Schema schema, Collection<Query> views, Map<String, Integer> bounds, boolean splitProducts) {
        super(schema, (Integer instNum) -> schema.makeConcreteInstance("instance" + instNum, bounds), (Instance inst1, Instance inst2) -> {
            MyZ3Context context = schema.getContext();
            List<BoolExpr> clauses = new ArrayList<>();
            clauses.addAll(inst1.getConstraints().values());
            clauses.addAll(inst2.getConstraints().values());
            if (splitProducts) {
                for (Query v : views) {
                    // (equal under each part) || (empty on one+ part per instance)
                    List<BoolExpr> equalityParts = new ArrayList<>();
                    List<BoolExpr> nonempty1Parts = new ArrayList<>();
                    List<BoolExpr> nonempty2Parts = new ArrayList<>();
                    Iterable<Query> components = v.getComponents();
                    for (Query q : components) {
                        equalityParts.add(q.apply(inst1).equalsExpr(q.apply(inst2)));
                        nonempty1Parts.add(context.mkNot(q.apply(inst1).isEmpty()));
                        nonempty2Parts.add(context.mkNot(q.apply(inst2).isEmpty()));
                    }
                    BoolExpr equality = context.mkAnd(equalityParts.toArray(new BoolExpr[0]));
                    BoolExpr nonempty1 = context.mkAnd(nonempty1Parts.toArray(new BoolExpr[0]));
                    BoolExpr nonempty2 = context.mkAnd(nonempty2Parts.toArray(new BoolExpr[0]));
                    clauses.add(
                            context.mkOr(
                                    equality,
                                    context.mkAnd(context.mkNot(nonempty1), context.mkNot(nonempty2))
                            )
                    );
                }
            } else {
                for (Query v : views) {
                    clauses.add(v.apply(inst1).equalsExpr(v.apply(inst2)));
                }
            }
            return clauses;
        });
    }
}
