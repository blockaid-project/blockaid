package edu.berkeley.cs.netsys.privacy_proxy.solver;

import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;

import java.util.HashMap;
import java.util.Map;

public class FixedBoundEstimator extends BoundEstimator {
    private final int bound;

    public FixedBoundEstimator(int bound) {
        this.bound = bound;
    }

    public Map<String, Integer> calculateBounds(Schema schema, UnmodifiableLinearQueryTrace trace) {
        Map<String, Integer> m = new HashMap<>();
        for (String relationName : schema.getRelationNames()) {
            m.put(relationName, bound);
        }
        return m;
    }

}
