package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Dependency;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Query;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Schema;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;

public record SubPreamble(Collection<Query> views, Collection<Dependency> dependencies) {
    public static SubPreamble fromPolicies(Schema schema, Collection<Policy> policies,
                                           Collection<Dependency> dependencies) {
        List<Query> views = policies.stream().map(p -> p.getSolverQuery(schema)).collect(Collectors.toList());
        return new SubPreamble(views, dependencies);
    }

    public static SubPreamble fromLabels(Schema schema, Iterable<PreambleLabel> labels) {
        ArrayList<Policy> policies = new ArrayList<>();
        ArrayList<Dependency> dependencies = new ArrayList<>();
        for (PreambleLabel l : labels) {
            switch (l.getKind()) {
                case VIEW -> policies.add(((ViewLabel) l).policy());
                case DEPENDENCY -> dependencies.add(((DependencyLabel) l).dependency());
                default -> throw new IllegalArgumentException("unrecognized preamble label: " + l);
            }
        }
        return SubPreamble.fromPolicies(schema, policies, dependencies);
    }
}
