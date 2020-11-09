package policy_checker;

import com.microsoft.z3.*;
import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.sql.*;
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
    private String relation;
    private Set<String> projectColumns;
    private Set<String> thetaColumns;
    private SqlBasicCall theta;
    private boolean usesSupserset;

    public Policy(Properties info, String sqlPolicy) {
        try {
            this.context = new QueryContext(info);
        }catch (PrivacyException e)
        {
            e.printStackTrace();
        }

        SqlNode parsedSql = parseSql(sqlPolicy);
        projectColumns = new HashSet<>();
        thetaColumns = new HashSet<>();

        SqlSelect sqlSelect = (SqlSelect) parsedSql;
        relation = ((SqlIdentifier) sqlSelect.getFrom()).names.get(0);
        for (SqlNode sn : sqlSelect.getSelectList()) {
            String column = ((SqlIdentifier) sn).names.get(0);
            projectColumns.add(relation + "." + column);
        }

        theta = (SqlBasicCall) sqlSelect.getWhere();
        if (theta != null) {
            addThetaColumns(theta);
        }

        usesSupserset = false;
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

    private void addThetaColumns(SqlBasicCall predicate) {
        SqlNode left = predicate.operand(0);
        SqlNode right = predicate.operand(1);
        if (left instanceof SqlBasicCall) {
            addThetaColumns((SqlBasicCall) left);
            addThetaColumns((SqlBasicCall) right);
        } else {
            if (left instanceof SqlIdentifier) {
                thetaColumns.add(relation + "." + ((SqlIdentifier) left).names.get(0));
            }
            if (right instanceof SqlIdentifier) {
                thetaColumns.add(relation + "." + ((SqlIdentifier) right).names.get(0));
            }
        }
    }

    public Set<String> getProjectColumns() {
        return projectColumns;
    }

    public Set<String> getThetaColumns() {
        return thetaColumns;
    }

    private Expr getPredicate(Context context, SqlNode theta) {
        if (theta instanceof SqlIdentifier) {
            return context.mkConst(context.mkSymbol(relation + "." + ((SqlIdentifier) theta).names.get(0)), context.getIntSort());
        } else if (theta instanceof SqlLiteral) {
            return context.mkInt(((SqlLiteral) theta).intValue(true));
        } else if (theta instanceof SqlBasicCall) {
            Expr left = getPredicate(context, ((SqlBasicCall) theta).operand(0));
            Expr right = getPredicate(context, ((SqlBasicCall) theta).operand(1));
            if (theta.getKind() == SqlKind.AND) {
                return context.mkAnd((BoolExpr) left, (BoolExpr) right);
            } else if (theta.getKind() == SqlKind.OR) {
                return context.mkOr((BoolExpr) left, (BoolExpr) right);
            } else if (theta.getKind() == SqlKind.EQUALS) {
                return context.mkEq(left, right);
            } else if (theta.getKind() == SqlKind.LESS_THAN) {
                return context.mkLt((ArithExpr) left, (ArithExpr) right);
            } else if (theta.getKind() == SqlKind.LESS_THAN_OR_EQUAL) {
                return context.mkLe((ArithExpr) left, (ArithExpr) right);
            } else if (theta.getKind() == SqlKind.GREATER_THAN) {
                return context.mkGt((ArithExpr) left, (ArithExpr) right);
            } else if (theta.getKind() == SqlKind.GREATER_THAN_OR_EQUAL) {
                return context.mkGe((ArithExpr) left, (ArithExpr) right);
            }
        }
        throw new UnsupportedOperationException("where clause uses unsupported operations: " + theta);
    }

    public BoolExpr getPredicate(Context context) {
        if (theta != null) {
            return (BoolExpr) getPredicate(context, theta);
        } else {
            return context.mkTrue();
        }
    }

    public boolean checkApplicable(Set<String> projectColumns, Set<String> thetaColumns) {
        if (!containsAny(this.projectColumns, projectColumns)) {
            return false;
        }

        if (usesSupserset && !containsAll(thetaColumns, this.thetaColumns)) {
            return false;
        }

        if (!usesSupserset && !containsAny(thetaColumns, this.thetaColumns)) {
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
}
