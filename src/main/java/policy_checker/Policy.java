package policy_checker;

import com.microsoft.z3.*;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;
import solver.Query;
import solver.Schema;
import sql.ParsedPSJ;
import sql.ParserResult;
import sql.SchemaPlusWithKey;

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
