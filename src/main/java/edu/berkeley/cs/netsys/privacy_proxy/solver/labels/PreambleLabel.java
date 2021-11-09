package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import java.util.regex.Pattern;

// Context-agnostic.
public interface PreambleLabel {
    enum Kind {
        DEPENDENCY,
        POLICY
    }

    Kind getKind();
}
