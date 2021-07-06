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
class PrivacyQueryEmptyRBWrapper extends PrivacyQuery {
    private final PrivacyQuery pq;

    public PrivacyQueryEmptyRBWrapper(PrivacyQuery pq) {
        super(pq);
        this.pq = pq;
    }

    @Override
    public List<String> getProjectColumns() {
        return pq.getProjectColumns();
    }

    @Override
    public List<String> getThetaColumns() {
        return pq.getThetaColumns();
    }

    @Override
    public List<String> getRelations() {
        return pq.getRelations();
    }

    @Override
    public Query getSolverQuery(Schema schema) {
        return pq.getSolverQuery(schema);
    }

    @Override
    public Query getSolverQuery(Schema schema, String paramPrefix, int offset) {
        return pq.getSolverQuery(schema, paramPrefix, offset);
    }

    @Override
    public List<Boolean> getResultBitmap() {
        return Collections.emptyList();
    }
}
