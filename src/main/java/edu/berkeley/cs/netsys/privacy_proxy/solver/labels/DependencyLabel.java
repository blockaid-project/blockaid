package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import edu.berkeley.cs.netsys.privacy_proxy.solver.Dependency;

public record DependencyLabel(Dependency dependency) implements PreambleLabel {
    @Override
    public Kind getKind() {
        return Kind.DEPENDENCY;
    }
}
