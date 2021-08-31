package solver;

import cache.trace.UnmodifiableLinearQueryTrace;

import java.util.Map;

public abstract class BoundEstimator {
    public abstract Map<String, Integer> calculateBounds(Schema schema, UnmodifiableLinearQueryTrace trace);
}
