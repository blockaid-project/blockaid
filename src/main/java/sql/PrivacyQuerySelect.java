package sql;

import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.SqlNodeList;
import org.apache.calcite.sql.SqlSelect;

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

public class PrivacyQuerySelect extends PrivacyQuery {
    private SqlNode where;
    private SqlNode from;
    private SqlNodeList selectAttributes;

    public PrivacyQuerySelect(ParserResult parsedSql) {
        this(parsedSql, new Object[0]);
    }

    public PrivacyQuerySelect(ParserResult parsedSql, Object[] parameters) {
        super(parsedSql, parameters);
        reduceQuery();
    }

    @Override
    public Set<String> getProjectColumns() {
        return new HashSet<>();
    }

    @Override
    public void reduceQuery(){
        SqlSelect select = (SqlSelect) parsedSql.sqlNode;
        where = select.getWhere();
        from =  select.getFrom();
        selectAttributes = select.getSelectList();
    }

    public SqlNode getWhere() {return where;}

    public SqlNode getFrom() {return from;}

    public SqlNodeList getSelectAttributes() {return selectAttributes;}

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        PrivacyQuerySelect that = (PrivacyQuerySelect) o;
        return Objects.equals(where, that.where) &&
                Objects.equals(from, that.from) &&
                Objects.equals(selectAttributes, that.selectAttributes);
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), where, from, selectAttributes);
    }
}
