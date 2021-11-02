package edu.berkeley.cs.netsys.privacy_proxy.solver;

import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.Map;

public abstract class BoundEstimator<C extends Z3ContextWrapper<?, ?, ?, ?>> {
    public abstract Map<String, Integer> calculateBounds(Schema<C> schema, UnmodifiableLinearQueryTrace trace);
}
