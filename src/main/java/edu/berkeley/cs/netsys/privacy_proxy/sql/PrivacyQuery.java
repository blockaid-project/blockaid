package edu.berkeley.cs.netsys.privacy_proxy.sql;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Query;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Schema;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.*;

public abstract class PrivacyQuery {
    public final ParserResult parserResult;
    public final ImmutableList<Object> parameters;
    public final ImmutableList<String> paramNames;

    /**
     * For making wrapper.  Doesn't copy the privacy query.
     * @param pq the privacy query to wrap over.
     */
    protected PrivacyQuery(PrivacyQuery pq) {
        this.parserResult = pq.parserResult;
        this.parameters = pq.parameters;
        this.paramNames = pq.paramNames;
    }

    public PrivacyQuery(ParserResult parserResult) {
        this(parserResult, Collections.emptyList(), Collections.emptyList());
    }

    public PrivacyQuery(ParserResult parserResult, List<Object> parameters, List<String> paramNames) {
        this.parserResult = parserResult;
        this.parameters = ImmutableList.copyOf(parameters);
        this.paramNames = ImmutableList.copyOf(paramNames);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        PrivacyQuery query = (PrivacyQuery) o;
        if (!parserResult.equals(query.parserResult)) return false;
        if (parameters.size() != query.parameters.size()) return false;
        for (int i = 0; i < parameters.size(); ++i) {
            if (paramNames.get(i).equals("?") && !parameters.get(i).equals(query.parameters.get(i))) return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int result = parserResult.hashCode();
        for (int i = 0; i < parameters.size(); ++i) {
            if (paramNames.get(i).equals("?")) {
                result = 31 * result + Objects.hash(parameters.get(i));
            }
        }
        return result;
    }

    public abstract Set<String> getAllNormalizedProjectColumns();
    public abstract Set<String> getProjectColumnsByIdx(int colIdx);
    public abstract Set<String> getNormalizedProjectColumnsByIdx(int colIdx);
    public abstract List<String> getThetaColumns();
    public abstract Set<String> getAllNormalizedThetaColumns();

    /**
     * Gets all relations referenced by this query.
     * @return an immutable set of all relations referenced by this query.
     */
    public abstract ImmutableSet<String> getRelations();

    // FIXME(zhangwen): these methods refer to sorts, etc.; belong in solver package?
    public abstract <C extends Z3ContextWrapper<?, ?, ?, ?>>
    Query<C> getSolverQuery(Schema<C> schema);

    public abstract <C extends Z3ContextWrapper<?, ?, ?, ?>>
    Query<C> getSolverQuery(Schema<C> schema, String paramPrefix, int offset);

    public abstract List<Boolean> getResultBitmap();
}
