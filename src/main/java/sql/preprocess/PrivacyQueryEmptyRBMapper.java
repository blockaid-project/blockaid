package sql.preprocess;

import solver.Query;
import solver.Schema;
import sql.PrivacyQuery;

import java.util.Collections;
import java.util.List;
import java.util.Set;

/**
 * Wrapper around a PrivacyQuery that returns empty for result bitmap.
 */
class PrivacyQueryEmptyRBMapper extends PrivacyQuery {
    private final PrivacyQuery pq;

    public PrivacyQueryEmptyRBMapper(PrivacyQuery pq) {
        super(pq);
        this.pq = pq;
    }

    @Override
    public Set<String> getProjectColumns() {
        return pq.getProjectColumns();
    }

    @Override
    public Set<String> getThetaColumns() {
        return pq.getThetaColumns();
    }

    @Override
    public Query getSolverQuery(Schema schema) {
        return pq.getSolverQuery(schema);
    }

    @Override
    public List<Boolean> getResultBitmap() {
        return Collections.emptyList();
    }
}
