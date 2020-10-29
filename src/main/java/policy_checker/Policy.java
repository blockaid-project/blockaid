package policy_checker;

import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;
import sql.PrivacyException;
import sql.QueryContext;

import java.util.Collection;
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;

public class Policy {
    private QueryContext context;
    private String sqlPolicy;
    private SqlNode parsedSql;
    private Set<String> projectColumns;
    private Set<String> thetaRelations;

    public Policy(Properties info, String sqlPolicy){
        this.sqlPolicy = sqlPolicy;
        try {
            this.context = new QueryContext(info);
        }catch (PrivacyException e)
        {
            e.printStackTrace();
        }

        parsedSql = parseSql(sqlPolicy);

        // todo

        projectColumns = new HashSet<>();
        thetaRelations = new HashSet<>();
    }

    public boolean checkPolicySchema(){
        return true;
    }

    private SqlNode parseSql(String sql){
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
            throw new RuntimeException("parse failed: " + e.getMessage(), e);
        }

        return sqlNode;
    }

    public Set<String> getProjectColumns() {
        return projectColumns;
    }

    public Set<String> getThetaRelations() {
        return thetaRelations;
    }

    public Object getPredicate() {
        throw new UnsupportedOperationException("todo");
    }
}
