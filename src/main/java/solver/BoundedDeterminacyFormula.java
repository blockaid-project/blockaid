package solver;

import com.google.common.collect.Iterables;
import com.google.common.collect.ListMultimap;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import solver.labels.ConstraintLabel;
import solver.labels.PreambleLabel;
import solver.labels.SubPreamble;
import solver.labels.ViewLabel;

import java.util.*;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;

public class BoundedDeterminacyFormula extends DeterminacyFormula {
    public BoundedDeterminacyFormula(Schema schema, Collection<Query> views, Map<String, Integer> bounds, boolean splitProducts) {
        this(schema, views, bounds, splitProducts, TextOption.USE_TEXT, null, null);
    }

    public BoundedDeterminacyFormula(Schema schema, Collection<Query> views, Map<String, Integer> bounds,
                                     boolean splitProducts, TextOption text,
                                     ListMultimap<String, Map<String, Object>> table2KnownRows,
                                     Collection<PreambleLabel> selectedPreamble) {
        super(schema, (Integer instNum) -> schema.makeConcreteInstance("instance" + instNum, bounds, table2KnownRows), (Instance inst1, Instance inst2) -> {
            MyZ3Context context = schema.getContext();
            List<BoolExpr> clauses = new ArrayList<>();

            checkArgument(inst1.getConstraints().keySet().equals(inst2.getConstraints().keySet()));
            SubPreamble sub = selectedPreamble == null ? SubPreamble.all(inst1, inst2, views)
                    : SubPreamble.fromLabels(selectedPreamble);

            for (Constraint c : sub.constraints()) {
                Iterables.addAll(clauses, inst1.getConstraints().get(c));
                Iterables.addAll(clauses, inst2.getConstraints().get(c));
            }

            Solver solver = context.mkSolver();
            solver.add(clauses.toArray(new BoolExpr[0]));

            if (splitProducts) {
                for (Query v : sub.views()) {
                    // (equal under each part) || (empty on one+ part per instance)
                    List<BoolExpr> equalityParts = new ArrayList<>();
                    List<BoolExpr> empty1Parts = new ArrayList<>();
                    List<BoolExpr> empty2Parts = new ArrayList<>();
                    for (Query q : v.getComponents()) {
                        Iterables.addAll(equalityParts, q.apply(inst1).equalsExpr(q.apply(inst2)));
                        empty1Parts.add(q.apply(inst1).isEmptyExpr());
                        empty2Parts.add(q.apply(inst2).isEmptyExpr());
                    }
                    BoolExpr equality = context.mkAnd(equalityParts.toArray(new BoolExpr[0]));
                    BoolExpr empty1 = context.mkOr(empty1Parts.toArray(new BoolExpr[0]));
                    BoolExpr empty2 = context.mkOr(empty2Parts.toArray(new BoolExpr[0]));
                    clauses.add(
                            context.mkOr(
                                    equality,
                                    context.mkAnd(empty1, empty2)
                            )
                    );
                }
            } else {
                for (Query v : sub.views()) {
                    Iterables.addAll(clauses, v.apply(inst1, solver).equalsExpr(v.apply(inst2, solver)));
                }
            }
            return clauses;
        }, text);
    }
}
