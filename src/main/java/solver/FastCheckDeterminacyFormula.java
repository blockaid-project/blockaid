package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import sql.QuerySequence;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class FastCheckDeterminacyFormula extends DeterminacyFormula{
    public FastCheckDeterminacyFormula(Context context, Schema schema, Collection<Query> views) {
        super(context, schema, views);

        List<BoolExpr> clauses = new ArrayList<>();
        if (inst1.constraint != null) {
            clauses.add(inst1.constraint);
        }
        if (inst2.constraint != null) {
            clauses.add(inst2.constraint);
        }
        for (Query v : views) {
            clauses.add(v.apply(context, inst1).isContainedIn(context, v.apply(context, inst2)));
        }
        setPreparedExpr(context.mkAnd(clauses.toArray(new BoolExpr[0])));
    }

    @Override
    public Expr[] makeFormulaConstants(QuerySequence queries) {
        /**
         *  Makes SMT formula for fast check: either "determinacy holds" or "I don't know".
         *
         *  Currently only supports PSJ / union of PSJ.
         */
        Query query = queries.get(queries.size() - 1).query.getSolverQuery(schema);
        Sort[] headTypes = query.headTypes();
        Expr[] freshConsts = new Expr[headTypes.length];
        for (int i = 0; i < freshConsts.length; ++i) {
            freshConsts[i] = context.mkFreshConst("z", headTypes[i]);
        }
        return freshConsts;
    }

    @Override
    public BoolExpr makeFormula(QuerySequence queries, Expr[] constants) {
        Query query = queries.get(queries.size() - 1).query.getSolverQuery(schema);
        Tuple extHeadTup = new Tuple(constants);
        return context.mkAnd(
                query.doesContain(context, inst1, extHeadTup),
                context.mkNot(query.doesContain(context, inst2, extHeadTup)),
                generateTupleCheck(queries)
        );
    }
}
