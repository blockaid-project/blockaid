package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import sql.QuerySequence;

import java.util.Collection;

public class FastCheckDeterminacyFormula extends DeterminacyFormula{
    public FastCheckDeterminacyFormula(Context context, Schema schema, Collection<Query> views) {
        super(context, schema, views);
    }

    @Override
    public BoolExpr makeFormula(QuerySequence queries) {
        /**
         *  Makes SMT formula for fast check: either "determinacy holds" or "I don't know".
         *
         *  Currently only supports PSJ / union of PSJ.
         */
        Query query = queries.get(queries.size() - 1).query.getSolverQuery(schema);
        Sort[] headTypes = query.headTypes();
        Expr[] freshConsts = new Expr[headTypes.length];
        for (int i = 0; i < freshConsts.length; ++i) {
            freshConsts[i] = context.mkFreshConst("v", headTypes[i]);
        }

        Tuple extHeadTup = new Tuple(freshConsts);
        return context.mkAnd(
                query.doesContain(context, inst1, extHeadTup),
                context.mkNot(query.doesContain(context, inst2, extHeadTup)),
                generateTupleCheck(queries),
                preparedExpr
        );
    }
}
