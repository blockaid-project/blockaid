package policy_checker;

import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;
import sql.PrivacyException;
import sql.QueryContext;

import java.util.Properties;
import java.util.Set;

public class Policy {
    private QueryContext context;
    private String[] sqlPolicy;
    public SqlNode[] parsedSql;
    public Set<String> thetaRelations;

    public Policy(Properties info, String[] sqlPolicy){
        this.sqlPolicy = sqlPolicy;
        try {
            this.context = new QueryContext(info);
        }catch (PrivacyException e)
        {
            e.printStackTrace();
        }

        parsedSql = new SqlNode[sqlPolicy.length];
        for(int i = 0; i < sqlPolicy.length; i++){
            parsedSql[i] = parseSql(sqlPolicy[i]);
        }
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
}
