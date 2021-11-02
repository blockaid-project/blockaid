package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Streams;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.SubPreamble;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;

public class BoundedDeterminacyFormula<C extends Z3ContextWrapper<?, ?, ?, ?>> extends DeterminacyFormula<C, BoundedInstance<C>> {
    private final ImmutableList<Expr<?>> allDbVars;

    public BoundedDeterminacyFormula(Schema<C> schema, ImmutableList<Policy> policies,
                                     Map<String, Integer> bounds, boolean splitProducts) {
        this(schema, policies, bounds, splitProducts, TextOption.USE_TEXT, null, null);
    }

    public BoundedDeterminacyFormula(Schema<C> schema, ImmutableList<Policy> policies,
                                     Map<String, Integer> bounds, boolean splitProducts, TextOption text,
                                     ListMultimap<String, Map<String, Object>> table2KnownRows,
                                     SubPreamble<C> subPreamble) {
        super(schema,
                (Integer instNum) -> schema.makeBoundedInstance("instance" + instNum, bounds, table2KnownRows),
                (BoundedInstance<C> inst1, BoundedInstance<C> inst2) -> {
                    checkArgument(inst1.getSchema() == schema && inst1.isBounded());
                    checkArgument(inst2.getSchema() == schema && inst2.isBounded());

                    C context = schema.getContext();
                    List<BoolExpr> clauses = new ArrayList<>();

                    SubPreamble<C> sub = subPreamble != null
                            ? subPreamble
                            : new SubPreamble<>(schema.getPolicyQueries(policies), schema.getDependencies());

                    for (Dependency d : sub.dependencies()) {
                        Iterables.addAll(clauses, d.apply(inst1));
                        Iterables.addAll(clauses, d.apply(inst2));
                    }

                    if (splitProducts) {
                        for (Query<C> v : sub.views()) {
                            // (equal under each part) || (empty on one+ part per instance)
                            List<BoolExpr> equalityParts = new ArrayList<>();
                            List<BoolExpr> empty1Parts = new ArrayList<>();
                            List<BoolExpr> empty2Parts = new ArrayList<>();
                            for (Query<C> q : v.getComponents()) {
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
                        for (Query<C> v : sub.views()) {
                            Iterables.addAll(clauses, v.apply(inst1).equalsExpr(v.apply(inst2)));
                        }
                    }
                    return clauses;
                }, text);

        this.allDbVars = Streams.concat(
                inst1.getAllVars().stream(),
                inst2.getAllVars().stream()
        ).collect(ImmutableList.toImmutableList());
    }

    public ImmutableList<Expr<?>> getAllDbVars() {
        return allDbVars;
    }
}
