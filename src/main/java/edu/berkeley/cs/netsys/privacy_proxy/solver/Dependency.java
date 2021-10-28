package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.BoolExpr;

import java.util.List;

// Context-agnostic.
// FIXME(zhangwen): Make a solver-independent version of this.
public interface Dependency {
    Iterable<BoolExpr> apply(Instance instance);
    List<String> getRelevantColumns(); // `table`.`column`.

    ImmutableSet<String> getFromRelations();
    ImmutableSet<String> getToRelations();
}
