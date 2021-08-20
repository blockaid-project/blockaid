package cache;

import cache.labels.EqualityLabel;
import cache.labels.Label;
import cache.labels.ReturnedRowLabel;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import policy_checker.Policy;
import solver.*;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;

class MyUnsatCoreDeterminacyFormula extends BoundedDeterminacyFormula {
    private final QueryTrace trace;
    private final ImmutableSet<String> relevantAttributes;

    public static MyUnsatCoreDeterminacyFormula create(Schema schema, Collection<Policy> policies,
                                                       Collection<Query> views, QueryTrace trace) {
        BoundEstimator boundEstimator = new UnsatCoreBoundEstimator(new FixedBoundEstimator(0));
        Map<String, Integer> bounds = boundEstimator.calculateBounds(schema, trace);
        Map<String, Integer> slackBounds = Maps.transformValues(bounds, n -> n + 1);
        return new MyUnsatCoreDeterminacyFormula(schema, policies, views, trace, slackBounds);
    }

    private MyUnsatCoreDeterminacyFormula(Schema schema, Collection<Policy> policies, Collection<Query> views,
                                          QueryTrace trace, Map<String, Integer> bounds) {
        super(schema, views, bounds, true, TextOption.NO_TEXT);
        this.trace = trace;
        this.relevantAttributes = policies.stream()
                .flatMap(policy -> policy.getThetaColumns().stream())
                .collect(ImmutableSet.toImmutableSet());
    }

    public Map<Label, BoolExpr> makeLabeledExprs() {
        MyZ3Context context = schema.getContext();
        QueryTraceEntry lastEntry = trace.getCurrentQuery();
        ArrayListMultimap<Object, Expr> ecs = ArrayListMultimap.create(); // Value -> constants that equal that value.

        Map<Expr, EqualityLabel.Operand> expr2Operand = new HashMap<>();
        Map<Label, BoolExpr> label2Expr = new HashMap<>();

        List<QueryTraceEntry> allEntries = trace.getAllEntries();
        for (int queryIdx = 0; queryIdx < allEntries.size(); ++queryIdx) {
            QueryTraceEntry e = allEntries.get(queryIdx);
            boolean isCurrentQuery = e == lastEntry;
            String qPrefix = (isCurrentQuery? "cq" : ("q" + queryIdx));
            Query q = e.getQuery().getSolverQuery(schema, qPrefix, 0);

            if (!e.hasTuples() && e != lastEntry) {
                // Discard this query -- it is not the query being checked, and it has returned no rows.
                continue;
            }

            List<Object> paramValues = e.getQuery().parameters;
            int numParams = paramValues.size();
            Expr[] paramExprs = new Expr[numParams];
            for (int i = 0; i < numParams; ++i) {
                paramExprs[i] = context.mkConst(
                        // TODO(zhangwen): this naming scheme has to match that in `ParsedPSJ`, which is error-prone.
                        "!" + qPrefix + "!" + i,
                        Tuple.getSortFromObject(context, paramValues.get(i)));
            }
            Tuple paramConstants = new Tuple(schema, paramExprs);

            for (int paramIdx = 0; paramIdx < numParams; ++paramIdx) {
                Expr paramExpr = paramConstants.get(paramIdx);
                Object v = paramValues.get(paramIdx);
                checkState(!expr2Operand.containsKey(paramExpr));
                expr2Operand.put(paramExpr, new EqualityLabel.QueryParamOperand(queryIdx, isCurrentQuery, paramIdx));
                ecs.put(v, paramExpr);
            }

            if (!e.hasTuples()) {
                continue;
            }

            Relation r1 = q.apply(inst1);
            Relation r2 = q.apply(inst2);
            List<List<Object>> tuples = e.getTuples();
            for (int rowIdx = 0; rowIdx < tuples.size(); ++rowIdx) {
                List<Object> tuple = tuples.get(rowIdx);
                String tupPrefix = "!" + qPrefix + "_tup" + rowIdx;

                Tuple head = q.makeHead(colIdx -> tupPrefix + "_col" + colIdx);
                for (int colIdx = 0; colIdx < tuple.size(); ++colIdx) {
                    Object v = tuple.get(colIdx);
                    if (v == null) {
                        continue;
                    }
                    // FIXME(zhangwen): eliminate irrelevant.
                    Expr fieldExpr = head.get(colIdx);
                    checkState(!expr2Operand.containsKey(fieldExpr));
                    expr2Operand.put(fieldExpr, new EqualityLabel.ReturnedRowFieldOperand(queryIdx, isCurrentQuery, rowIdx, colIdx));
                    ecs.put(v, fieldExpr);
                }

                Label l = new ReturnedRowLabel(queryIdx, rowIdx);
                label2Expr.put(l, context.mkAnd(r1.doesContainExpr(head), r2.doesContainExpr(head)));
            }
        }

        for (Map.Entry<String, Integer> e : trace.getConstMap().entrySet()) {
            // FIXME(zhangwen): currently assumes that the concrete value of constant is irrelevant.
            // TODO(zhangwen): should put const naming scheme in one place.
            String name = e.getKey();
            Expr constExpr = context.mkConst("!" + name, context.getCustomIntSort());
            expr2Operand.put(constExpr, new EqualityLabel.ContextConstantOperand(name));
            ecs.put(e.getValue(), constExpr);
        }

        for (Object value : ecs.keySet()) {
            // Generate equalities of the form: variable = value.
            Expr vExpr = Tuple.getExprFromObject(context, value);
            List<Expr> variables = ecs.get(value);
            {
                EqualityLabel.ValueOperand rhs = new EqualityLabel.ValueOperand(value);
                for (Expr p : variables) {
                    label2Expr.put(
                            new EqualityLabel(expr2Operand.get(p), rhs),
                            context.mkEq(p, vExpr)
                    );
                }
            }

            // Generate equalities of the form: variable1 = variable2.
            for (int i = 0; i < variables.size(); ++i) {
                Expr p1 = variables.get(i);
                EqualityLabel.Operand lhs = expr2Operand.get(p1);
                for (int j = i + 1; j < variables.size(); ++j) {
                    Expr p2 = variables.get(j);
                    EqualityLabel.Operand rhs = expr2Operand.get(p2);
                    label2Expr.put(new EqualityLabel(lhs, rhs), context.mkEq(p1, p2));
                }
            }
        }

        return label2Expr;
    }

    public List<BoolExpr> makeMainFormula() {
        Query query = trace.getCurrentQuery().getQuery().getSolverQuery(schema, "cq", 0);
        Tuple extHeadTup = query.makeFreshHead();

        ArrayList<BoolExpr> formulas = new ArrayList<>(preamble);
        formulas.add(query.doesContain(inst1, extHeadTup));
        formulas.add(context.mkNot(query.doesContain(inst2, extHeadTup)));
        return formulas;
    }

    @Override
    public Iterable<BoolExpr> makeCompleteFormula(QueryTrace queries) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Iterable<BoolExpr> makeBodyFormula(QueryTrace queries) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String generateSMT(QueryTrace queries) {
        throw new UnsupportedOperationException();
    }
}
