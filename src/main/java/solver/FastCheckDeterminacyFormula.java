package solver;

import cache.QueryTrace;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class FastCheckDeterminacyFormula extends DeterminacyFormula{
    public FastCheckDeterminacyFormula(Schema schema, Collection<Query> views) {
        super(schema, (Instance inst1, Instance inst2) -> {
            List<BoolExpr> clauses = new ArrayList<>();
            if (inst1.constraint != null) {
                clauses.add(inst1.constraint);
            }
            if (inst2.constraint != null) {
                clauses.add(inst2.constraint);
            }
            for (Query v : views) {
                clauses.add(v.apply(inst1).isContainedIn(v.apply(inst2)));
            }
            return schema.getContext().mkAnd(clauses.toArray(new BoolExpr[0]));
        });
    }

    /**
     *  Makes SMT formula for fast check: either "determinacy holds" or "I don't know".
     */
    @Override
    public Expr[] makeFormulaConstants(QueryTrace queries) {
        Query query = queries.getCurrentQuery().getQuery().getSolverQuery(schema);
        Sort[] headTypes = query.headTypes();
        Expr[] freshConsts = new Expr[headTypes.length];
        for (int i = 0; i < freshConsts.length; ++i) {
            freshConsts[i] = context.mkFreshConst("z", headTypes[i]);
        }
        return freshConsts;
    }

    @Override
    public BoolExpr makeFormula(QueryTrace queries, Expr[] constants) {
        Query query = queries.getCurrentQuery().getQuery().getSolverQuery(schema);
        Tuple extHeadTup = new Tuple(schema, constants);
        return context.mkAnd(
                query.doesContain(inst1, extHeadTup),
                context.mkNot(query.doesContain(inst2, extHeadTup)),
                generateTupleCheck(queries, constants)
        );
    }
}
