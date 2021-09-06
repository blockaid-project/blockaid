package solver;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.*;
import sql.*;

import java.sql.SQLException;
import java.util.*;

public class ImportedDependency implements Dependency {
    private final PrivacyQuery q1;
    private final PrivacyQuery q2;
    private final ImmutableList<String> relevantColumns;

    public ImportedDependency(String dependency, SchemaPlusWithKey schema, Parser parser) throws SQLException {
        String[] parts = dependency.split(";", 2);
        q1 = PrivacyQueryFactory.createPrivacyQuery(parser.parse(parts[0]), schema, Collections.emptyList(), Collections.emptyList());
        q2 = PrivacyQueryFactory.createPrivacyQuery(parser.parse(parts[1]), schema, Collections.emptyList(), Collections.emptyList());

        relevantColumns = new ImmutableList.Builder<String>()
                .addAll(q1.getAllNormalizedProjectColumns())
                .addAll(q1.getAllNormalizedThetaColumns())
                .addAll(q2.getAllNormalizedProjectColumns())
                .addAll(q2.getAllNormalizedThetaColumns())
                .build();
    }

    @Override
    public List<String> getFromRelations() {
        return q1.getRelations();
    }

    @Override
    public List<String> getToRelations() {
        return q2.getRelations();
    }

    @Override
    public Iterable<BoolExpr> apply(Instance instance) {
        Schema schema = instance.schema;
        Query solverQuery1 = q1.getSolverQuery(schema);
        Query solverQuery2 = q2.getSolverQuery(schema);

        return solverQuery1.apply(instance).isContainedInExpr(solverQuery2.apply(instance));
    }

    @Override
    public List<String> getRelevantColumns() {
        return relevantColumns;
    }
}
