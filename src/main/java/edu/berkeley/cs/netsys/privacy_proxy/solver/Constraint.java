package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.BoolExpr;

import java.util.List;

// Context-agnostic.
public interface Constraint {
    Iterable<BoolExpr> apply(Instance instance);
    List<String> getRelevantColumns();
}
