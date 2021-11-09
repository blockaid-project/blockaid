package edu.berkeley.cs.netsys.privacy_proxy.policy_checker;

import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Query;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Schema;
import edu.berkeley.cs.netsys.privacy_proxy.sql.ParsedPSJ;
import edu.berkeley.cs.netsys.privacy_proxy.sql.ParserResult;
import edu.berkeley.cs.netsys.privacy_proxy.sql.SchemaPlusWithKey;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;

public class Policy {
    private final ParserResult parserResult;
    private final ParsedPSJ parsedPSJ;
    private final boolean useSuperset;

    public Policy(SchemaPlusWithKey schema, ParserResult result) {
        this.parserResult = result;
        SqlNode node = result.getSqlNode();
        checkArgument(node.getKind() == SqlKind.SELECT, "a view must be a SELECT, instead got: " + node.getKind());
        parsedPSJ = new ParsedPSJ(node, schema, Collections.emptyList(), Collections.emptyList());
        useSuperset = false;
    }

    public ParsedPSJ getParsedPSJ() {
        return parsedPSJ;
    }

    public Set<String> getProjectColumns() {
        return new HashSet<>(parsedPSJ.getProjectColumns());
    }

    public Set<String> getThetaColumns() {
        return new HashSet<>(parsedPSJ.getThetaColumns());
    }

    public Set<String> getNormalizedThetaColumns() {
        return new HashSet<>(parsedPSJ.getNormalizedThetaColumns());
    }

    public <C extends Z3ContextWrapper<?, ?, ?, ?>> BoolExpr getPredicate(Schema<C> schema) {
        return parsedPSJ.getPredicate(schema);
    }

    public boolean hasNoTheta() {
        return parsedPSJ.hasNoTheta();
    }

    public boolean checkApplicable(Set<String> projectColumns, Set<String> thetaColumns) {
        if (Collections.disjoint(parsedPSJ.getProjectColumns(), projectColumns)) {
            return false;
        }

        if (useSuperset && !thetaColumns.containsAll(parsedPSJ.getThetaColumns())) {
            return false;
        }

        return useSuperset || parsedPSJ.getThetaColumns().isEmpty()
                || !Collections.disjoint(thetaColumns, parsedPSJ.getThetaColumns());
    }

    public <C extends Z3ContextWrapper<?, ?, ?, ?>> Query<C> getSolverQuery(Schema<C> schema) {
        return parsedPSJ.getSolverQuery(schema);
    }

    @Override
    public String toString() {
        return parserResult.getParsedSql();
    }
}
