package sql;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import solver.Query;
import solver.Schema;

import java.util.*;

public abstract class PrivacyQuery {
    public final ParserResult parsedSql;
    public final ImmutableList<Object> parameters;
    public final ImmutableList<String> paramNames;

    /**
     * For making wrapper.  Doesn't copy the privacy query.
     * @param pq the privacy query to wrap over.
     */
    protected PrivacyQuery(PrivacyQuery pq)
    {
        this.parsedSql = pq.parsedSql;
        this.parameters = pq.parameters;
        this.paramNames = pq.paramNames;
    }

    public PrivacyQuery(ParserResult parsedSql)
    {
        this(parsedSql, Collections.emptyList(), Collections.emptyList());
    }

    public PrivacyQuery(ParserResult parsedSql, List<Object> parameters, List<String> paramNames)
    {
        this.parsedSql = parsedSql;
        this.parameters = ImmutableList.copyOf(parameters);
        this.paramNames = ImmutableList.copyOf(paramNames);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        PrivacyQuery query = (PrivacyQuery) o;
        if (!parsedSql.equals(query.parsedSql)) return false;
        if (parameters.size() != query.parameters.size()) return false;
        for (int i = 0; i < parameters.size(); ++i) {
            if (paramNames.get(i).equals("?") && !parameters.get(i).equals(query.parameters.get(i))) return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int result = Objects.hash(parsedSql);
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
