package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import sql.QuerySequence;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class BasicDeterminacyFormula extends DeterminacyFormula {
    public BasicDeterminacyFormula(Context context, Schema schema, Collection<Query> views) {
        super(context, schema, views);

        List<BoolExpr> clauses = new ArrayList<>();
        if (inst1.constraint != null) {
            clauses.add(inst1.constraint);
        }
        if (inst2.constraint != null) {
            clauses.add(inst2.constraint);
        }
        assert views.size() > 0;
        for (Query v : views) {
            clauses.add(v.apply(context, inst1).equalsExpr(context, v.apply(context, inst2)));
        }
        setPreparedExpr(context.mkAnd(clauses.toArray(new BoolExpr[0])));
    }

    @Override
    public Expr[] makeFormulaConstants(QuerySequence queries) {
        return new Expr[0];
    }

    @Override
    public BoolExpr makeFormula(QuerySequence queries, Expr[] constants) {
        Query query = queries.lastInTrace().query.getSolverQuery(schema);
        return context.mkAnd(
                context.mkNot(query.apply(context, inst1).equalsExpr(context, query.apply(context, inst2))),
                generateTraceConformanceExpr(queries)
        );
    }
}
