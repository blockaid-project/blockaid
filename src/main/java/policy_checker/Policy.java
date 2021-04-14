package policy_checker;

import com.microsoft.z3.*;
import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.*;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;
import solver.Query;
import solver.Schema;
import sql.ParsedPSJ;
import sql.PrivacyException;
import sql.QueryContext;

import java.util.*;

public class Policy {
    private ParsedPSJ parsedPSJ;
    private boolean useSuperset;

    public Policy(QueryContext context, SchemaPlus schema, String sqlPolicy) {
        parsedPSJ = new ParsedPSJ(parseSql(context, sqlPolicy), schema, Collections.emptyList(), Collections.emptyList());
        useSuperset = false;
    }

    public boolean checkPolicySchema(){
        return true;
    }

    private SqlNode parseSql(QueryContext context, String sql){
        final CalciteConnectionConfig config = context.getCfg();
        SqlParser parser = SqlParser.create(sql,
                SqlParser.configBuilder()
                        .setQuotedCasing(config.quotedCasing())
                        .setUnquotedCasing(config.unquotedCasing())
                        .setQuoting(config.quoting())
                        .build());
        SqlNode sqlNode;
        try {
            sqlNode = parser.parseStmt();
        } catch (SqlParseException e) {
            throw new RuntimeException("parse failed: " + e.getMessage() + " for query " + sql, e);
        }

        return sqlNode;
    }

    public Set<String> getProjectColumns() {
        return new HashSet<>(parsedPSJ.getProjectColumns());
    }

    public Set<String> getThetaColumns() {
        return new HashSet<>(parsedPSJ.getThetaColumns());
    }

    public BoolExpr getPredicate(Context context) {
        return parsedPSJ.getPredicate(context);
    }

    public boolean checkApplicable(Set<String> projectColumns, Set<String> thetaColumns) {
        if (!containsAny(parsedPSJ.getProjectColumns(), projectColumns)) {
            return false;
        }

        if (useSuperset && !containsAll(thetaColumns, parsedPSJ.getThetaColumns())) {
            return false;
        }

        if (!useSuperset && !parsedPSJ.getThetaColumns().isEmpty() && !containsAny(thetaColumns, parsedPSJ.getThetaColumns())) {
            return false;
        }

        return true;
    }

    private boolean containsAll(Collection<String> set, Collection<String> query) {
        return set.containsAll(query);
    }

    private boolean containsAny(Collection<String> set, Collection<String> query) {
        for (String s : query) {
            if (set.contains(s)) {
                return true;
            }
        }
        return false;
    }

    public Query getSolverQuery(Schema schema) {
        return parsedPSJ.getSolverQuery(schema);
    }
}
