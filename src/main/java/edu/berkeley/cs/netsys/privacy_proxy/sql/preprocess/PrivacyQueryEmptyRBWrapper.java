package edu.berkeley.cs.netsys.privacy_proxy.sql.preprocess;

import com.google.common.collect.ImmutableSet;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Query;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Schema;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;

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
    public Set<String> getAllNormalizedProjectColumns() {
        return pq.getAllNormalizedProjectColumns();
    }

    @Override
    public Set<String> getProjectColumnsByIdx(int colIdx) {
        return pq.getProjectColumnsByIdx(colIdx);
    }

    @Override
    public Set<String> getNormalizedProjectColumnsByIdx(int colIdx) {
        return pq.getNormalizedProjectColumnsByIdx(colIdx);
    }

    @Override
    public List<String> getThetaColumns() {
        return pq.getThetaColumns();
    }

    @Override
    public Set<String> getAllNormalizedThetaColumns() {
        return pq.getAllNormalizedThetaColumns();
    }

    @Override
    public ImmutableSet<String> getRelations() {
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
