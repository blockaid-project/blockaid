package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.sql.*;
import org.apache.calcite.sql.SqlKind;

import java.util.*;

public class ImportedDependency implements Dependency {
    private final PrivacyQuery q1;
    private final PrivacyQuery q2;
    private final ImmutableList<String> relevantColumns;

    // Constraint: lhs is subset of rhs.
    public ImportedDependency(SchemaPlusWithKey rawSchema, ParserResult lhs, ParserResult rhs) {
        q1 = PrivacyQueryFactory.createPrivacyQuery(lhs, rawSchema, Collections.emptyList(), Collections.emptyList());
        q2 = PrivacyQueryFactory.createPrivacyQuery(rhs, rawSchema, Collections.emptyList(), Collections.emptyList());

        relevantColumns = new ImmutableList.Builder<String>()
                .addAll(q1.getAllNormalizedProjectColumns())
                .addAll(q1.getAllNormalizedThetaColumns())
                .addAll(q2.getAllNormalizedProjectColumns())
                .addAll(q2.getAllNormalizedThetaColumns())
                .build();
    }

    @Override
    public ImmutableSet<String> getFromRelations() {
        return q1.getRelations();
    }

    @Override
    public ImmutableSet<String> getToRelations() {
        return q2.getRelations();
    }

    @Override
    public ImmutableSet<String> getCriticalRelations() {
        if (!(q1 instanceof PrivacyQuerySelect pqs)) {
            // TODO(zhangwen): implement for union and empty wrapper.
            return ImmutableSet.of();
        }
        return pqs.getRelations();
    }

    @Override
    public <C extends Z3ContextWrapper<?, ?, ?, ?>> Iterable<BoolExpr> apply(Instance<C> instance) {
        Schema<C> schema = instance.getSchema();
        Query<C> solverQuery1 = q1.getSolverQuery(schema);
        Query<C> solverQuery2 = q2.getSolverQuery(schema);

        return solverQuery1.apply(instance).isContainedInExpr(solverQuery2.apply(instance));
    }

    @Override
    public List<String> getRelevantColumns() {
        return relevantColumns;
    }
}
