package sql;

import java.util.Arrays;
import java.util.Objects;
import java.util.Set;

public abstract class PrivacyQuery {
    protected ParserResult parsedSql;
    protected Object[] parameters;

    public PrivacyQuery(ParserResult parsedSql)
    {
        this(parsedSql, new Object[0]);
    }

    public PrivacyQuery(ParserResult parsedSql, Object[] parameters)
    {
        this.parsedSql = parsedSql;
        this.parameters = new Object[parameters.length];
        for (int i = 0; i < parameters.length; ++i) {
            this.parameters[i] = parameters[i];
        }
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        PrivacyQuery query = (PrivacyQuery) o;
        return parsedSql.equals(query.parsedSql) &&
                Arrays.equals(parameters, query.parameters);
    }

    @Override
    public int hashCode() {
        int result = Objects.hash(parsedSql);
        result = 31 * result + Arrays.hashCode(parameters);
        return result;
    }

    abstract public void reduceQuery();
    abstract public Set<String> getProjectColumns();
}

