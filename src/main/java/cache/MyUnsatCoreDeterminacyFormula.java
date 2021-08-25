package cache;

import cache.labels.EqualityLabel;
import cache.labels.Label;
import cache.labels.ReturnedRowLabel;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import policy_checker.Policy;
import solver.*;

import java.util.*;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkState;
import static util.TerminalColor.ANSI_RED;
import static util.TerminalColor.ANSI_RESET;

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
        // TODO(zhangwen): don't compute this all the time.
        this.relevantAttributes = Stream.concat(
                policies.stream().flatMap(policy -> policy.getNormalizedThetaColumns().stream()),
                schema.getDependencies().stream().flatMap(c -> c.getRelevantColumns().stream())
        ).collect(ImmutableSet.toImmutableSet());
    }

    public Map<Label, BoolExpr> makeLabeledExprs() {
        MyZ3Context context = schema.getContext();
        QueryTraceEntry lastEntry = trace.getCurrentQuery();
        ArrayListMultimap<Object, Expr> ecs = ArrayListMultimap.create(); // Value -> constants that equal that value.

        Map<Expr, EqualityLabel.Operand> expr2Operand = new HashMap<>();
        Map<Label, BoolExpr> label2Expr = new HashMap<>();

        List<QueryTraceEntry> allEntries = trace.getAllEntries();
        Set<Expr> pkValuedExprs = new HashSet<>();
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
            List<List<Object>> rows = e.getTuples();

            ImmutableSet<String> pkValuedColumns = schema.getRawSchema().getPkValuedColumns();

            for (int rowIdx = 0; rowIdx < rows.size(); ++rowIdx) {
                List<Object> tuple = rows.get(rowIdx);
                String tupPrefix = "!" + qPrefix + "_tup" + rowIdx;

                Tuple head = q.makeHead(colIdx -> tupPrefix + "_col" + colIdx);
                for (int attrIdx = 0; attrIdx < tuple.size(); ++attrIdx) {
                    Object v = tuple.get(attrIdx);
                    if (v == null) {
                        continue;
                    }
                    // Ignore irrelevant columns.
                    Set<String> attrNames = e.getQuery().getProjectColumnsByIdx(attrIdx);
                    if (attrNames.stream().noneMatch(relevantAttributes::contains)) {
                        continue;
                    }
                    Expr attrExpr = head.get(attrIdx);
                    checkState(!expr2Operand.containsKey(attrExpr));
                    expr2Operand.put(attrExpr, new EqualityLabel.ReturnedRowFieldOperand(queryIdx, isCurrentQuery, rowIdx, attrIdx));
                    ecs.put(v, attrExpr);

                    if (attrNames.stream().anyMatch(pkValuedColumns::contains)) {
                        pkValuedExprs.add(attrExpr);
                    }
                }

                Label l = new ReturnedRowLabel(queryIdx, rowIdx);
                label2Expr.put(l, context.mkAnd(r1.doesContainExpr(head), r2.doesContainExpr(head)));
            }
        }

        long startTime = System.currentTimeMillis();
        removeRedundantExprs(
                ecs,
                expr2Operand,
                pkValuedExprs,
                label2Expr.values() // At this point, `label2Expr` only contains `ReturnedRowLabel`s.
        );
        System.out.println("\t\t| removeRedundantExprs:\t" + (System.currentTimeMillis() - startTime));

        for (Map.Entry<String, Integer> e : trace.getConstMap().entrySet()) {
            // FIXME(zhangwen): currently assumes that the concrete value of constant is irrelevant.
            // TODO(zhangwen): should put const naming scheme in one place.
            String name = e.getKey();
            Expr constExpr = context.mkConst("!" + name, context.getCustomIntSort());
            expr2Operand.put(constExpr, new EqualityLabel.ContextConstantOperand(name));
            ecs.put(e.getValue(), constExpr);
        }

        for (Object value : ecs.keySet()) {
            List<Expr> variables = ecs.get(value);
            System.out.println(ANSI_RED + value + ":\t" + variables.size() + "\t" + variables + ANSI_RESET);

            // Generate equalities of the form: variable = value.
            Expr vExpr = Tuple.getExprFromObject(context, value);
            if (vExpr != null) {
                // TODO(zhangwen): we currently ignore NULL values, i.e., assuming NULLs are irrelevant for compliance.
                EqualityLabel.ValueOperand rhs = new EqualityLabel.ValueOperand(value);
                for (Expr p : variables) {
                    if (pkValuedExprs.contains(p)) {
                        // Optimization based on assumption: the primary key value doesn't matter.
                        continue;
                    }
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

    // Optimization: For two operands that are always equal, remove one of them (from `ecs` & `expr2Operand`);
    // if one operand is a pk-valued expr, and add the other to `pkValuedExprs`.
    private void removeRedundantExprs(ArrayListMultimap<Object, Expr> ecs,
                                      Map<Expr, EqualityLabel.Operand> expr2Operand,
                                      Set<Expr> pkValuedExprs,
                                      Collection<BoolExpr> returnedRowExprs) {
        Solver solver = context.mkRawSolver();
        solver.add(returnedRowExprs.toArray(new BoolExpr[0]));

        for (Object v : ecs.keySet()) {
            HashSet<Expr> redundantExprs = new HashSet<>();
            List<Expr> variables = ecs.get(v);
            for (Expr p1 : variables) {
                EqualityLabel.Operand o1 = expr2Operand.get(p1);
                // Only look at labels of the form "query param = returned row attribute".
                if (o1.getKind() != EqualityLabel.Operand.Kind.QUERY_PARAM) {
                    continue;
                }

                for (Expr p2 : variables) {
                    EqualityLabel.Operand o2 = expr2Operand.get(p2);
                    if (o2.getKind() != EqualityLabel.Operand.Kind.RETURNED_ROW_ATTR) {
                        continue;
                    }

                    if (solver.check(context.mkNot(context.mkEq(p1, p2))) == Status.UNSATISFIABLE) {
                        // Keep the query param, toss the returned row attribute.
                        redundantExprs.add(p2);
                        if (pkValuedExprs.contains(p2)) {
                            pkValuedExprs.add(p1);
                        }
                    }
                }
            }

            variables.removeAll(redundantExprs);
            expr2Operand.keySet().removeAll(redundantExprs);
        }
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