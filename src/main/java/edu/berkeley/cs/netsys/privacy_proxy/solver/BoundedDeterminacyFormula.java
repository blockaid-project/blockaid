package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Lists;
import com.microsoft.z3.BoolExpr;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.PreambleLabel;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.SubPreamble;
import edu.berkeley.cs.netsys.privacy_proxy.util.Options;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.PRUNE_PREAMBLE;

public class BoundedDeterminacyFormula extends DeterminacyFormula {
    public BoundedDeterminacyFormula(Schema schema, ImmutableList<Policy> policies, Map<String, Integer> bounds, boolean splitProducts) {
        this(schema, policies, bounds, splitProducts, TextOption.USE_TEXT, null, null);
    }

    public BoundedDeterminacyFormula(Schema schema, ImmutableList<Policy> policies, Map<String, Integer> bounds,
                                     boolean splitProducts, TextOption text,
                                     ListMultimap<String, Map<String, Object>> table2KnownRows,
                                     Collection<PreambleLabel> selectedPreamble) {
        super(schema, (Integer instNum) -> schema.makeConcreteInstance("instance" + instNum, bounds, table2KnownRows), (Instance inst1, Instance inst2) -> {
            Z3ContextWrapper context = schema.getContext();
            List<BoolExpr> clauses = new ArrayList<>();

            checkArgument(inst1.getConstraints().keySet().equals(inst2.getConstraints().keySet()));
            SubPreamble sub = selectedPreamble == null || PRUNE_PREAMBLE == Options.OnOffType.OFF
                    ? SubPreamble.all(inst1, inst2, schema.getPolicyQueries(policies))
                    : SubPreamble.fromLabels(schema, selectedPreamble);

            for (Constraint c : sub.constraints()) {
                Iterables.addAll(clauses, inst1.getConstraints().get(c));
                Iterables.addAll(clauses, inst2.getConstraints().get(c));
            }

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
                    Iterables.addAll(clauses, v.apply(inst1).equalsExpr(v.apply(inst2)));
                }
            }
            return clauses;
        }, text);
    }

    @Override
    protected Iterable<BoolExpr> generateNotContains(Query query) {
        // Keep the formula quantifier-free.
        Tuple extHeadTup = query.makeFreshHead();
        List<BoolExpr> body = Lists.newArrayList(query.apply(inst1).doesContainExpr(extHeadTup));
        body.add(context.mkNot(
                context.mkAnd(query.apply(inst2).doesContainExpr(extHeadTup))
        ));
        return body;
    }
}
