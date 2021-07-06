package solver;

import com.microsoft.z3.*;
import sql.*;

import java.sql.SQLException;
import java.util.*;

public class ImportedDependency implements Dependency {
    private final PrivacyQuery q1;
    private final PrivacyQuery q2;

    public ImportedDependency(String dependency, SchemaPlusWithKey schema, Parser parser) throws SQLException {
        String[] parts = dependency.split(";", 2);
        q1 = PrivacyQueryFactory.createPrivacyQuery(parser.parse(parts[0]), schema, new Object[0], Collections.emptyList(), Collections.emptyMap());
        q2 = PrivacyQueryFactory.createPrivacyQuery(parser.parse(parts[1]), schema, new Object[0], Collections.emptyList(), Collections.emptyMap());
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
    public BoolExpr apply(Instance instance) {
        Schema schema = instance.schema;
        Query solverQuery1 = q1.getSolverQuery(schema);
        Query solverQuery2 = q2.getSolverQuery(schema);

        return solverQuery1.apply(instance).isContainedIn(solverQuery2.apply(instance));
    }
}
