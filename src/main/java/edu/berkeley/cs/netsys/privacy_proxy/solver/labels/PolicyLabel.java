package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;

public record PolicyLabel(Policy policy) implements PreambleLabel {
    @Override
    public Kind getKind() {
        return Kind.POLICY;
    }
}
