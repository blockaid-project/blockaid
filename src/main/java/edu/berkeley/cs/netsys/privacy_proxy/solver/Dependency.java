package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.BoolExpr;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.List;

// A dependency is of the form `LHS \subseteq RHS`.  Context-agnostic.
// FIXME(zhangwen): Make a solver-independent version of this.
public interface Dependency {
    <C extends Z3ContextWrapper<?, ?, ?, ?>> Iterable<BoolExpr> apply(Instance<C> instance);
    List<String> getRelevantColumns(); // `table`.`column`.

    // Relations referenced in the LHS query.
    ImmutableSet<String> getFromRelations();
    // Relations referenced in the RHS query.
    ImmutableSet<String> getToRelations();

    // These are relations that, if empty, will guarantee the dependency is satisfied.
    ImmutableSet<String> getCriticalRelations();
}
