package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import edu.berkeley.cs.netsys.privacy_proxy.solver.Query;

public record ViewLabel(Query query) implements PreambleLabel {
    @Override
    public Kind getKind() {
        return Kind.VIEW;
    }
}
