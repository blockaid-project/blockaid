package edu.berkeley.cs.netsys.privacy_proxy.policy_checker;

import com.microsoft.z3.*;
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
    private final ParsedPSJ parsedPSJ;
    private final boolean useSuperset;

    public Policy(SchemaPlusWithKey schema, ParserResult result) {
        SqlNode node = result.getSqlNode();
        checkArgument(node.getKind() == SqlKind.SELECT, "a view must be a SELECT, instead got: " + node.getKind());
        parsedPSJ = new ParsedPSJ(node, schema, Collections.emptyList(), Collections.emptyList());
        useSuperset = false;
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

    public BoolExpr getPredicate(Schema schema) {
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

    public Query getSolverQuery(Schema schema) {
        return parsedPSJ.getSolverQuery(schema);
    }
}
