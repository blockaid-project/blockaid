package sql;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.*;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;
import solver.PSJ;
import solver.Query;
import solver.Schema;
import solver.Tuple;

import java.util.*;

public class PrivacyQuerySelect extends PrivacyQuery {
    private SqlNode where;
    private SqlNode from;
    private SqlNodeList selectAttributes;
    private ParsedPSJ parsedPSJ;

    public PrivacyQuerySelect(ParserResult parsedSql, SchemaPlus schema) {
        this(parsedSql, schema, new Object[0], Collections.emptyList());
    }

    public PrivacyQuerySelect(ParserResult parsedSql, SchemaPlus schema, Object[] parameters, List<String> paramNames) {
        super(parsedSql, parameters, paramNames);
        reduceQuery();
        parsedPSJ = new ParsedPSJ(getSelectNode(parsedSql), schema, Arrays.asList(parameters), paramNames);
    }

    private SqlSelect getSelectNode(ParserResult result) {
        if (result.getSqlNode() instanceof SqlOrderBy) {
            return (SqlSelect) ((SqlOrderBy) result.getSqlNode()).query;
        } else {
            return (SqlSelect) result.getSqlNode();
        }
    }

    public boolean checkPolicySchema(){
        return true;
    }

    @Override
    public Set<String> getProjectColumns() {
        return new HashSet<>(parsedPSJ.getProjectColumns());
    }

    @Override
    public Set<String> getThetaColumns() {
        return new HashSet<>(parsedPSJ.getThetaColumns());
    }

    @Override
    public void reduceQuery(){
        SqlSelect select = getSelectNode(parsedSql);
        System.out.println("\t\t| reduceQuery: " + parsedSql + ", " + select);
        where = select.getWhere();
        from =  select.getFrom();
        selectAttributes = select.getSelectList();
    }

    @Override
    public Query getSolverQuery(Schema schema) {
        return parsedPSJ.getSolverQuery(schema);
    }

    public SqlNode getWhere() {return where;}

    public SqlNode getFrom() {return from;}

    public SqlNodeList getSelectAttributes() {return selectAttributes;}
}
