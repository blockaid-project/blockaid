package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

public interface PreambleLabel {
    enum Kind {
        CONSTRAINT,
        VIEW;
    }

    Kind getKind();
}
