package sql;

import solver.Query;
import solver.Schema;

import java.util.*;

public abstract class PrivacyQuery {
    public ParserResult parsedSql;
    public List<Object> parameters;
    public List<String> paramNames;

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

    public PrivacyQuery(ParserResult parsedSql, List<Object> parameters, List<String> paramNames)
    {
        this.parsedSql = parsedSql;
        this.parameters = parameters;
        this.paramNames = paramNames;
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

    abstract public Set<String> getProjectColumns();
    abstract public Set<String> getThetaColumns();
    abstract public Query getSolverQuery(Schema schema);
    abstract public List<Boolean> getResultBitmap();
}

