package cache;

import cache.labels.EqualityLabel;
import cache.labels.Label;
import cache.labels.ReturnedRowLabel;
import cache.trace.QueryTraceEntry;
import cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.ArrayListMultimap;
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

public class MyUnsatCoreDeterminacyFormula extends FastCheckDeterminacyFormula {
    protected final UnmodifiableLinearQueryTrace trace;

    public MyUnsatCoreDeterminacyFormula(Schema schema, Collection<Query> views, UnmodifiableLinearQueryTrace trace) {
        super(schema, views, TextOption.NO_TEXT);
        this.trace = trace;
    }

    public Map<ReturnedRowLabel, BoolExpr> makeLabeledExprs() {
        Map<ReturnedRowLabel, BoolExpr> label2Expr = new HashMap<>();
        List<QueryTraceEntry> allEntries = trace.getAllEntries();
        for (int queryIdx = 0; queryIdx < allEntries.size(); ++queryIdx) {
            QueryTraceEntry qte = allEntries.get(queryIdx);
            Query query = qte.getQuery().getSolverQuery(schema);
            Relation r1 = query.apply(inst1);
            Relation r2 = query.apply(inst2);
            List<Tuple> tuples = qte.getTuplesStream().map(
                    tuple -> new Tuple(schema, tuple.stream().map(
                            v -> Tuple.getExprFromObject(context, v)
                    ))).collect(Collectors.toList());

            for (int rowIdx = 0; rowIdx < tuples.size(); ++rowIdx) {
                Tuple tuple = tuples.get(rowIdx);
                ReturnedRowLabel l = new ReturnedRowLabel(queryIdx, rowIdx);
                label2Expr.put(l, context.mkAnd(Iterables.concat(r1.doesContainExpr(tuple), r2.doesContainExpr(tuple))));
            }
        }
        return label2Expr;
    }

    // Makes formula that is not under consideration for unsat core.
    public Iterable<BoolExpr> makeBackgroundFormulas() {
        ArrayList<BoolExpr> formulas = new ArrayList<>(preamble);
        Iterables.addAll(formulas, generateConstantCheck(trace));
        Iterables.addAll(formulas, generateNotContains(trace));
        return formulas;
    }
}
