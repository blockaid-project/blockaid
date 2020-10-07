package sql;

public abstract class PrivacyQuery {

    protected ParserResult parsedSql;

    public PrivacyQuery(ParserResult parsedSql)
    {
        this.parsedSql = parsedSql;
    }

    abstract public boolean equals(Object obj);

    abstract public void reduceQuery();

}

