package sql;

import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.sql.*;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;

import java.util.*;

public class PrivacyQuerySelect extends PrivacyQuery {
    private SqlNode where;
    private SqlNode from;
    private SqlNodeList selectAttributes;
    private Set<String> projectColumns;
    private Set<String> thetaColumns;

    public PrivacyQuerySelect(ParserResult parsedSql) {
        this(parsedSql, new Object[0]);
    }

    public PrivacyQuerySelect(ParserResult parsedSql, Object[] parameters) {
        super(parsedSql, parameters);
        reduceQuery();


        projectColumns = new HashSet<>();
        thetaColumns = new HashSet<>();

        SqlSelect sqlSelect = (SqlSelect) parsedSql.getSqlNode();
        SqlNode fromClause = sqlSelect.getFrom();
        String relation = null;
        if (fromClause.getKind() != SqlKind.JOIN) {
            relation = ((SqlIdentifier) sqlSelect.getFrom()).names.get(1);
        }
        for (SqlNode sn : sqlSelect.getSelectList()) {
            addQualifiedColumnName(projectColumns, relation, (SqlIdentifier) sn);
        }

        SqlBasicCall theta = (SqlBasicCall) sqlSelect.getWhere();
        if (theta != null) {
            addThetaColumns(relation, theta);
        }
    }

    public boolean checkPolicySchema(){
        return true;
    }

    private void addThetaColumns(String relation, SqlBasicCall predicate) {
        SqlNode left = predicate.operand(0);
        SqlNode right = predicate.operand(1);
        if (left instanceof SqlBasicCall) {
            addThetaColumns(relation, (SqlBasicCall) left);
            addThetaColumns(relation, (SqlBasicCall) right);
        } else {
            if (left instanceof SqlIdentifier) {
                addQualifiedColumnName(thetaColumns, relation, (SqlIdentifier) left);
            }
            if (right instanceof SqlIdentifier) {
                addQualifiedColumnName(thetaColumns, relation, (SqlIdentifier) right);
            }
        }
    }

    private void addQualifiedColumnName(Set<String> set, String relation, SqlIdentifier identifier) {
        List<String> names = identifier.names;
        if (names.size() == 1) {
            if (relation == null) {
                throw new UnsupportedOperationException("joins must only use fully-specified column names");
            }
            set.add((relation + "." + ((SqlIdentifier) identifier).names.get(0)).toUpperCase());
        } else {
            set.add((names.get(0) + "." + names.get(1)).toUpperCase());
        }
    }

    @Override
    public Set<String> getProjectColumns() {
        return projectColumns;
    }

    @Override
    public Set<String> getThetaColumns() {
        return thetaColumns;
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
