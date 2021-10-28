package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.microsoft.z3.BoolExpr;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;

public class BasicDeterminacyFormula extends DeterminacyFormula {
    public BasicDeterminacyFormula(Schema schema, ImmutableList<Policy> policySet, TextOption textOption) {
        super(schema,
                (Integer instNum) -> schema.makeFreshInstance("instance" + instNum),
                (Instance inst1, Instance inst2) -> {
                    checkArgument(inst1.getSchema() == schema);
                    checkArgument(inst2.getSchema() == schema);

                    List<BoolExpr> clauses = new ArrayList<>();
                    for (Dependency d : schema.getDependencies()) {
                        Iterables.addAll(clauses, d.apply(inst1));
                        Iterables.addAll(clauses, d.apply(inst2));
                    }
                    for (Query v : schema.getPolicyQueries(policySet)) {
                        Iterables.addAll(clauses, v.apply(inst1).equalsExpr(v.apply(inst2)));
                    }
                    return clauses;
                }, textOption);
    }

    public BasicDeterminacyFormula(Schema schema, ImmutableList<Policy> policySet) {
        this(schema, policySet, TextOption.USE_TEXT);
    }
}
