package solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import solver.context.MyZ3Context;
import solver.labels.ConstraintLabel;
import solver.labels.PreambleLabel;
import solver.labels.ReturnedRowLabel;
import cache.trace.QueryTraceEntry;
import cache.trace.UnmodifiableLinearQueryTrace;
import com.microsoft.z3.BoolExpr;
import solver.labels.ViewLabel;

import java.util.*;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;

/**
 * Labels returned rows for unsat core extraction with Vampire (uses fast unsat).
 */
public class RRLVampireDeterminacyFormula extends DeterminacyFormula {
    private final ImmutableList<Constraint> constraints;
    private final ImmutableList<Query> views;

    private static final Pattern RR_PATTERN = Pattern.compile("ReturnedRowLabel!(\\d+)!(\\d+)");
    private static final Pattern PREAMBLE_PATTERN = Pattern.compile("(Constraint|View)!(\\d+)");

    public RRLVampireDeterminacyFormula(Schema schema, List<Query> views) {
        super(schema,
                (Integer instNum) -> schema.makeFreshInstance("instance" + instNum),
                (Instance inst1, Instance inst2) -> {
                    MyZ3Context context = schema.getContext();
                    List<BoolExpr> clauses = new ArrayList<>();

                    Map<Constraint, Iterable<BoolExpr>> c1 = inst1.getConstraints(), c2 = inst2.getConstraints();
                    checkArgument(c1.keySet().equals(c2.keySet()));
                    int i = 0;
                    for (Constraint c : c1.keySet()) {
                        BoolExpr boolConst = context.mkBoolConst("Constraint!" + i);
                        clauses.add(context.mkImplies(boolConst, context.mkAnd(
                                Iterables.concat(c1.get(c), c2.get(c))
                        )));
                        clauses.add(boolConst);
                        ++i;
                    }

                    i = 0;
                    for (Query v : views) {
                        BoolExpr boolConst = context.mkBoolConst("View!" + i);
                        clauses.add(context.mkImplies(boolConst,
                                context.mkAnd(v.apply(inst1).isContainedInExpr(v.apply(inst2)))));
                        clauses.add(boolConst);
                        ++i;
                    }
                    return clauses;
                }, TextOption.USE_TEXT);

        this.constraints = ImmutableList.copyOf(inst1.getConstraints().keySet());
        this.views = ImmutableList.copyOf(views);
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
                // This way, we can construct an unsat core by looking for the name of `boolConst` in Vampire proof.
                exprs.add(context.mkImplies(boolConst, context.mkAnd(r1.doesContainExpr(tuple))));
                exprs.add(boolConst);
            }
        }

        return exprs;
    }

    public Set<ReturnedRowLabel> extractRRLabels(String output) {
        return RR_PATTERN.matcher(output).results()
                .map(r -> new ReturnedRowLabel(Integer.parseInt(r.group(1)), Integer.parseInt(r.group(2))))
                .collect(Collectors.toSet());
    }

    public Set<PreambleLabel> extractPreambleLabels(String output) {
        return PREAMBLE_PATTERN.matcher(output).results()
                .map(r -> {
                    int i = Integer.parseInt(r.group(2));
                    return switch (r.group(1)) {
                        case "Constraint" -> new ConstraintLabel(constraints.get(i));
                        case "View" -> new ViewLabel(views.get(i));
                        default -> throw new IllegalArgumentException("parse preamble label failed: " + r.group(0));
                    };
                }).collect(Collectors.toSet());
    }
}
