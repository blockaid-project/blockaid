package solver;

import solver.labels.ReturnedRowLabel;
import cache.trace.QueryTraceEntry;
import cache.trace.UnmodifiableLinearQueryTrace;
import com.microsoft.z3.BoolExpr;

import java.util.*;

/**
 * Labels returned rows for unsat core extraction with Vampire.
 */
public class RRLVampireDeterminacyFormula extends FastCheckDeterminacyFormula {
    public RRLVampireDeterminacyFormula(Schema schema, Collection<Query> views) {
        super(schema, views, TextOption.USE_TEXT);
    }

    @Override
    protected Iterable<BoolExpr> generateTupleCheck(UnmodifiableLinearQueryTrace trace) {
        ArrayList<BoolExpr> exprs = new ArrayList<>();

        List<QueryTraceEntry> allEntries = trace.getAllEntries();
        for (int queryIdx = 0; queryIdx < allEntries.size(); ++queryIdx) {
            QueryTraceEntry qte = allEntries.get(queryIdx);
            if (!qte.hasTuples()) {
                continue;
            }
            Query query = qte.getQuery().getSolverQuery(schema);
            Relation r1 = query.apply(inst1);
            List<Tuple> tuples = getTupleObjects(qte, schema);

            for (int rowIdx = 0; rowIdx < tuples.size(); ++rowIdx) {
                Tuple tuple = tuples.get(rowIdx);
                ReturnedRowLabel l = new ReturnedRowLabel(queryIdx, rowIdx);
                BoolExpr boolConst = context.mkBoolConst(l.toString());
                // This way, we can construct an unsat core by looking for the name of `boolCosnt` in Vampire proof.
                exprs.add(context.mkImplies(boolConst, context.mkAnd(r1.doesContainExpr(tuple))));
                exprs.add(boolConst);
            }
        }

        return exprs;
    }
}
