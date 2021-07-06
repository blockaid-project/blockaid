package solver;

import cache.QueryTrace;

import java.util.Map;

public abstract class BoundEstimator {
    public abstract Map<String, Integer> calculateBounds(Schema schema, QueryTrace trace);
}
