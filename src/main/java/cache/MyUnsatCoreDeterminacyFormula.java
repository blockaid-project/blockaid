package cache;

import cache.labels.EqualityLabel;
import cache.labels.Label;
import cache.labels.ReturnedRowLabel;
import cache.trace.QueryTraceEntry;
import cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import policy_checker.Policy;
import solver.*;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkState;
import static util.TerminalColor.ANSI_RED;
import static util.TerminalColor.ANSI_RESET;

/**
 * Marks returned row labels, for use with Vampire.
 */
public class MyUnsatCoreDeterminacyFormula extends FastCheckDeterminacyFormula {
    public MyUnsatCoreDeterminacyFormula(Schema schema, Collection<Query> views) {
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
                exprs.add(context.mkImplies(boolConst, context.mkAnd(r1.doesContainExpr(tuple))));
                exprs.add(boolConst);
            }
        }

        return exprs;
    }
}
