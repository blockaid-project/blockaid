package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.microsoft.z3.BoolExpr;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;

public class FastCheckDeterminacyFormula<C extends Z3ContextWrapper<?, ?, ?, ?>> extends DeterminacyFormula<C, Instance<C>> {
    public FastCheckDeterminacyFormula(Schema<C> schema, ImmutableList<Policy> policySet, TextOption textOption) {
        super(schema,
                (Integer instNum) -> schema.makeFreshInstance("instance" + instNum),
                (Instance<C> inst1, Instance<C> inst2) -> {
                    checkArgument(inst1.getSchema() == schema);
                    checkArgument(inst2.getSchema() == schema);

                    List<BoolExpr> clauses = new ArrayList<>();
                    for (Dependency d : schema.getDependencies()) {
                        Iterables.addAll(clauses, d.apply(inst1));
                        Iterables.addAll(clauses, d.apply(inst2));
                    }
                    for (Query<C> v : schema.getPolicyQueries(policySet)) {
                        Iterables.addAll(clauses, v.apply(inst1).isContainedInExpr(v.apply(inst2)));
                    }
                    return clauses;
                }, textOption);
    }

    public FastCheckDeterminacyFormula(Schema<C> schema, ImmutableList<Policy> policySet) {
        this(schema, policySet, TextOption.USE_TEXT);
    }
}
