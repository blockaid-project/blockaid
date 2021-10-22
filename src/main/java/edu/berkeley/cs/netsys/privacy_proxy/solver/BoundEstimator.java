package edu.berkeley.cs.netsys.privacy_proxy.solver;

import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;

import java.util.Map;

public abstract class BoundEstimator {
    public abstract Map<String, Integer> calculateBounds(Schema schema, UnmodifiableLinearQueryTrace trace);
}
