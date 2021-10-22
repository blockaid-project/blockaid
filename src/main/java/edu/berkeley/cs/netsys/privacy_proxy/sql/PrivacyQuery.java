package edu.berkeley.cs.netsys.privacy_proxy.sql;

import com.google.common.collect.ImmutableList;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Query;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Schema;

import java.util.*;

public abstract class PrivacyQuery {
    public final ParserResult parserResult;
    public final ImmutableList<Object> parameters;
    public final ImmutableList<String> paramNames;

    /**
     * For making wrapper.  Doesn't copy the privacy query.
     * @param pq the privacy query to wrap over.
     */
    protected PrivacyQuery(PrivacyQuery pq)
    {
        this.parserResult = pq.parserResult;
        this.parameters = pq.parameters;
        this.paramNames = pq.paramNames;
    }

    public PrivacyQuery(ParserResult parserResult)
    {
        this(parserResult, Collections.emptyList(), Collections.emptyList());
    }

    public PrivacyQuery(ParserResult parserResult, List<Object> parameters, List<String> paramNames)
    {
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

    abstract public Set<String> getAllNormalizedProjectColumns();
    abstract public Set<String> getProjectColumnsByIdx(int colIdx);
    abstract public Set<String> getNormalizedProjectColumnsByIdx(int colIdx);
    abstract public List<String> getThetaColumns();
    abstract public Set<String> getAllNormalizedThetaColumns();
    abstract public List<String> getRelations();
    abstract public Query getSolverQuery(Schema schema);
    abstract public Query getSolverQuery(Schema schema, String paramPrefix, int offset);
    abstract public List<Boolean> getResultBitmap();
}
