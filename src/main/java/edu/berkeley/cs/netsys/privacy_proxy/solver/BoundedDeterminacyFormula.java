package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.*;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.DependencyLabel;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.PreambleLabel;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.PolicyLabel;
import edu.berkeley.cs.netsys.privacy_proxy.util.LogLevel;
import edu.berkeley.cs.netsys.privacy_proxy.util.Logger;
import org.checkerframework.checker.nullness.qual.Nullable;

import java.util.*;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;

public class BoundedDeterminacyFormula<C extends Z3ContextWrapper<?, ?, ?, ?>> extends DeterminacyFormula<C, BoundedInstance<C>> {
    private final ImmutableList<Expr<?>> allDbVars;

    public BoundedDeterminacyFormula(Schema<C> schema, ImmutableList<Policy> policies,
                                     Map<String, Integer> bounds, boolean splitProducts) {
        this(schema, policies, bounds, splitProducts, TextOption.USE_TEXT, null, null);
    }

    public BoundedDeterminacyFormula(Schema<C> schema, ImmutableList<Policy> policies,
                                     Map<String, Integer> bounds, boolean splitProducts, TextOption text,
                                     @Nullable ListMultimap<String, Map<String, Object>> table2KnownRows,
                                     @Nullable Collection<PreambleLabel> preambleLabels) {
        super(schema,
                (Integer instNum) -> schema.makeBoundedInstance("instance" + instNum, bounds, table2KnownRows),
                (BoundedInstance<C> inst1, BoundedInstance<C> inst2) -> {
                    checkArgument(inst1.getSchema() == schema && inst1.isBounded());
                    checkArgument(inst2.getSchema() == schema && inst2.isBounded());

                    C context = schema.getContext();
                    ImmutableMap.Builder<PreambleLabel, ImmutableList<BoolExpr>> builder = ImmutableMap.builder();

                    {
                        Stream<DependencyLabel> depLabels;
                        if (preambleLabels == null) {
                            depLabels = schema.getDependencies().stream().map(DependencyLabel::new);
                        } else {
                            depLabels = preambleLabels.stream()
                                    .filter(l -> l.getKind() == DependencyLabel.Kind.DEPENDENCY)
                                    .map(l -> (DependencyLabel) l);
                        }
                        depLabels.forEach(l -> builder.put(l, ImmutableList.copyOf(
                                Iterables.concat(l.dependency().apply(inst1), l.dependency().apply(inst2))
                        )));
                    }

                    {
                        Stream<PolicyLabel> viewLabels;
                        if (preambleLabels == null) {
                            viewLabels = policies.stream().map(PolicyLabel::new);
                        } else {
                            viewLabels = preambleLabels.stream()
                                    .filter(l -> l.getKind() == DependencyLabel.Kind.POLICY)
                                    .map(l -> (PolicyLabel) l);
                        }

                        if (splitProducts) {
                            viewLabels.forEach(l -> {
                                long startNs = System.nanoTime();
                                Query<C> v = l.policy().getSolverQuery(schema);

                                // (equal under each part) || (empty on one+ part per instance)
                                List<BoolExpr> equalityParts = new ArrayList<>();
                                List<BoolExpr> empty1Parts = new ArrayList<>();
                                List<BoolExpr> empty2Parts = new ArrayList<>();
                                for (Query<C> q : v.getComponents()) {
                                    Iterables.addAll(equalityParts, q.apply(inst1).equalsExpr(q.apply(inst2)));
                                    Iterables.addAll(empty1Parts, q.apply(inst1).isEmptyExpr());
                                    Iterables.addAll(empty2Parts, q.apply(inst2).isEmptyExpr());
                                }
                                BoolExpr equality = context.mkAnd(equalityParts.toArray(new BoolExpr[0]));
                                BoolExpr empty1 = context.mkOr(empty1Parts.toArray(new BoolExpr[0]));
                                BoolExpr empty2 = context.mkOr(empty2Parts.toArray(new BoolExpr[0]));

                                builder.put(l, ImmutableList.of(
                                        context.mkOr(
                                                equality,
                                                context.mkAnd(empty1, empty2)
                                        )
                                ));

                                long durMs = (System.nanoTime() - startNs) / 1000000;
                                if (durMs > 5000) {
                                    Logger.printMessage(() -> "Slow bounded view " + l + ":\t" + durMs, LogLevel.VERBOSE);
                                }
                            });
                        } else {
                            viewLabels.forEach(l -> {
                                Query<C> q = l.policy().getSolverQuery(schema);
                                builder.put(l, ImmutableList.copyOf(q.apply(inst1).equalsExpr(q.apply(inst2))));
                            });
                        }
                    }

                    return builder.build();
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
