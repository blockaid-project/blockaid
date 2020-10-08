package sql;

import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.SqlNodeList;
import org.apache.calcite.sql.SqlSelect;

public class PrivacyQuerySelect extends PrivacyQuery{
    private ParserResult parsedSql;
    private SqlNode where;
    private SqlNode from;
    private SqlNodeList selectAttributes;

    public PrivacyQuerySelect(ParserResult parsedSql){
        super(parsedSql);
        this.parsedSql = parsedSql;
        reduceQuery();
    }

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
    public int hashCode() {
        int result = 1;
        if (where != null) {
            result = 31 * result + where.toString().hashCode();
        }
        if (from != null) {
            result = 31 * result + from.toString().hashCode();
        }
        if (selectAttributes != null) {
            result = 31 * result + selectAttributes.toString().hashCode();
        }
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof PrivacyQuerySelect) {
            PrivacyQuerySelect other = (PrivacyQuerySelect) obj;
            return hashCode() == other.hashCode();
        }
        return false;
    }
}
