package policy_checker;

import com.microsoft.z3.*;
import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.config.Lex;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.*;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;
import solver.Query;
import solver.Schema;
import sql.ParsedPSJ;
import sql.PrivacyException;
import sql.QueryContext;
import sql.SchemaPlusWithKey;

import java.util.*;

public class Policy {
    private final ParsedPSJ parsedPSJ;
    private final boolean useSuperset;

    public Policy(QueryContext context, SchemaPlusWithKey schema, String sqlPolicy) {
        parsedPSJ = new ParsedPSJ(parseSql(context, sqlPolicy), schema, Collections.emptyList(), Collections.emptyList());
        useSuperset = false;
    }

    private SqlNode parseSql(QueryContext context, String sql){
        final CalciteConnectionConfig config = context.getCfg();
        SqlParser parser = SqlParser.create(sql,
                SqlParser.configBuilder()
                        .setQuotedCasing(config.quotedCasing())
                        .setUnquotedCasing(config.unquotedCasing())
                        .setQuoting(config.quoting())
                        .setLex(Lex.MYSQL)
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

    public BoolExpr getPredicate(Schema schema) {
        return parsedPSJ.getPredicate(schema);
    }

    public boolean hasNoTheta() {
        return parsedPSJ.hasNoTheta();
    }

    public boolean checkApplicable(Set<String> projectColumns, Set<String> thetaColumns) {
        if (!containsAny(parsedPSJ.getProjectColumns(), projectColumns)) {
            return false;
        }

        if (useSuperset && !thetaColumns.containsAll(parsedPSJ.getThetaColumns())) {
            return false;
        }

        return useSuperset || parsedPSJ.getThetaColumns().isEmpty() || containsAny(thetaColumns, parsedPSJ.getThetaColumns());
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
