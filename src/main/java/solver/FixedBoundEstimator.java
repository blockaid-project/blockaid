package solver;

import cache.QueryTrace;

import java.util.HashMap;
import java.util.Map;

public class FixedBoundEstimator extends BoundEstimator {
    private final int bound;

    public FixedBoundEstimator(int bound) {
        this.bound = bound;
    }

    public Map<String, Integer> calculateBounds(Schema schema, QueryTrace trace) {
        Map<String, Integer> m = new HashMap<>();
        for (String relationName : schema.getRelationNames()) {
            m.put(relationName, bound);
        }
        return m;
    }

}
