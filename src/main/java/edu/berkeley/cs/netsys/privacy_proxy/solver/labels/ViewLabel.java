package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;

public record ViewLabel(Policy policy) implements PreambleLabel {
    @Override
    public Kind getKind() {
        return Kind.VIEW;
    }
}
