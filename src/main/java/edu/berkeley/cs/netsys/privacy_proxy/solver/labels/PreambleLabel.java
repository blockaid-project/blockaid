package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

// Context-agnostic.
public interface PreambleLabel {
    enum Kind {
        DEPENDENCY,
        VIEW
    }

    Kind getKind();
}
