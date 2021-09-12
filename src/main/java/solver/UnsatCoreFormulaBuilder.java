package solver;

import cache.trace.QueryTraceEntry;
import cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.*;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import policy_checker.Policy;
import solver.labels.*;

import java.util.*;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class UnsatCoreFormulaBuilder {
    private final DeterminacyFormula baseFormula;
    private final ImmutableSet<String> relevantAttributes;

    // Shorthands.
    private final Schema schema;
    private final MyZ3Context context;

    public UnsatCoreFormulaBuilder(DeterminacyFormula baseFormula, Collection<Policy> policies) {
        this.baseFormula = baseFormula;
        this.schema = baseFormula.schema;
        this.context = baseFormula.context;

        this.relevantAttributes = Stream.concat(
                policies.stream().flatMap(policy -> policy.getNormalizedThetaColumns().stream()),
                schema.getDependencies().stream().flatMap(c -> c.getRelevantColumns().stream())
        ).collect(ImmutableSet.toImmutableSet());
    }

    public static class Formulas<L extends Label> {
        private final ImmutableMap<L, BoolExpr> labeledExprs;
        // Formula that is not under consideration for unsat core.
        private final ImmutableList<BoolExpr> background;

        public Formulas(Map<L, BoolExpr> labeledExprs, Collection<BoolExpr> background) {
            this.labeledExprs = ImmutableMap.copyOf(labeledExprs);
            this.background = ImmutableList.copyOf(background);
        }

        public ImmutableMap<L, BoolExpr> getLabeledExprs() {
            return labeledExprs;
        }

        public ImmutableList<BoolExpr> getBackground() {
            return background;
        }
    }

    public Formulas<ReturnedRowLabel> buildReturnedRowsOnly(UnmodifiableLinearQueryTrace trace) {
        ImmutableMap<ReturnedRowLabel, BoolExpr> labeledExprs = makeLabeledExprsRR(trace);
        ImmutableList.Builder<BoolExpr> bgBuilder = new ImmutableList.Builder<>();
        bgBuilder.addAll(baseFormula.preamble);
        bgBuilder.addAll(baseFormula.generateConstantCheck(trace));
        bgBuilder.addAll(baseFormula.generateNotContains(trace));
        return new Formulas<>(labeledExprs, bgBuilder.build());
    }

    // Assumes the entire trace is present, i.e., returned-row labels count as background.
    public Formulas<Label> buildParamRelationsOnly(UnmodifiableLinearQueryTrace trace) {
        Map<Label, BoolExpr> allLabeledExprs = makeLabeledExprsAll(trace);
        ImmutableList.Builder<BoolExpr> bgBuilder = new ImmutableList.Builder<>();

        bgBuilder.addAll(baseFormula.preamble);
        Query query = trace.getCurrentQuery().getQuery().getSolverQuery(schema, "cq", 0);
        Tuple extHeadTup = query.makeFreshHead();
        bgBuilder.addAll(query.apply(baseFormula.inst1).doesContainExpr(extHeadTup));
        bgBuilder.add(context.mkNot(context.mkAnd(query.apply(baseFormula.inst2).doesContainExpr(extHeadTup))));

        // Since we're param labels-only, add returned-row labels to background and exclude them from `labeledExprs`.
        ImmutableMap.Builder<Label, BoolExpr> labeledExprsBuilder = new ImmutableMap.Builder<>();
        for (Map.Entry<Label, BoolExpr> entry : allLabeledExprs.entrySet()) {
            if (entry.getKey().getKind() == Label.Kind.RETURNED_ROW) {
                bgBuilder.add(entry.getValue());
            } else {
                labeledExprsBuilder.put(entry);
            }
        }
        return new Formulas<>(labeledExprsBuilder.build(), bgBuilder.build());
    }

    // Once again, assumes the entire trace is present.
    public String buildValidateParamRelationsOnlySMT(UnmodifiableLinearQueryTrace trace, Set<Label> labels) {
        return baseFormula.generateSMT(() -> {
            Formulas<Label> fs = buildParamRelationsOnly(trace);
            return Iterables.concat(
                    fs.getBackground(),
                    Maps.filterKeys(fs.getLabeledExprs(), labels::contains).values()
            );
        });
    }

    private ImmutableMap<ReturnedRowLabel, BoolExpr> makeLabeledExprsRR(UnmodifiableLinearQueryTrace trace) {
        ImmutableMap.Builder<ReturnedRowLabel, BoolExpr> label2Expr = new ImmutableMap.Builder<>();
        List<QueryTraceEntry> allEntries = trace.getAllEntries();
        for (int queryIdx = 0; queryIdx < allEntries.size(); ++queryIdx) {
            QueryTraceEntry qte = allEntries.get(queryIdx);
            if (!qte.hasTuples()) {
                continue;
            }
            Query query = qte.getQuery().getSolverQuery(schema);
            Relation r1 = query.apply(baseFormula.inst1);
            List<Tuple> tuples = DeterminacyFormula.getTupleObjects(qte, schema);

            for (int rowIdx = 0; rowIdx < tuples.size(); ++rowIdx) {
                Tuple tuple = tuples.get(rowIdx);
                ReturnedRowLabel l = new ReturnedRowLabel(queryIdx, rowIdx);
                label2Expr.put(l, context.mkAnd(r1.doesContainExpr(tuple)));
            }
        }
        return label2Expr.build();
    }

    private Map<Label, BoolExpr> makeLabeledExprsAll(UnmodifiableLinearQueryTrace trace) {
        QueryTraceEntry lastEntry = trace.getCurrentQuery();
        ArrayListMultimap<Object, Expr> ecs = ArrayListMultimap.create(); // Value -> constants that equal that value.

        Map<Expr, Operand> expr2Operand = new HashMap<>();
        Map<Label, BoolExpr> label2Expr = new HashMap<>();

        List<QueryTraceEntry> allEntries = trace.getAllEntries();
        Set<Expr> pkValuedExprs = new HashSet<>();
        for (int queryIdx = 0; queryIdx < allEntries.size(); ++queryIdx) {
            QueryTraceEntry e = allEntries.get(queryIdx);
            boolean isCurrentQuery = e == lastEntry;
            String qPrefix = (isCurrentQuery? "cq" : ("q" + queryIdx));
            Query q = e.getQuery().getSolverQuery(schema, qPrefix, 0);

            if (!e.hasTuples() && !isCurrentQuery) {
                // Discard this query -- it has no returned rows, and it is not the query being checked.
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
                expr2Operand.put(paramExpr, new QueryParamOperand(queryIdx, isCurrentQuery, paramIdx));
                ecs.put(v, paramExpr);
            }

            if (!e.hasTuples()) {
                continue;
            }

            Relation r1 = q.apply(baseFormula.inst1);
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
                    checkState(!isCurrentQuery);
                    expr2Operand.put(attrExpr, new ReturnedRowFieldOperand(queryIdx, rowIdx, attrIdx));
                    ecs.put(v, attrExpr);

                    if (attrNames.stream().anyMatch(pkValuedColumns::contains)) {
                        pkValuedExprs.add(attrExpr);
                    }
                }

                Label l = new ReturnedRowLabel(queryIdx, rowIdx);
                label2Expr.put(l, context.mkAnd(r1.doesContainExpr(head)));
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

        for (Map.Entry<String, Object> e : trace.getConstMap().entrySet()) {
            // FIXME(zhangwen): currently assumes that the concrete value of constant is irrelevant.
            // TODO(zhangwen): should put const naming scheme in one place.
            String name = e.getKey();
            Object value = e.getValue();
            Expr constExpr = context.mkConst("!" + name, Tuple.getSortFromObject(context, value));
            expr2Operand.put(constExpr, new ContextConstantOperand(name));
            ecs.put(value, constExpr);
        }

        for (Object value : ecs.keySet()) {
            List<Expr> variables = ecs.get(value);
//            System.out.println(ANSI_RED + value + ":\t" + variables.size() + "\t" + variables + ANSI_RESET);

            // Generate equalities of the form: variable = value.
            Expr vExpr = Tuple.getExprFromObject(context, value);
            if (vExpr != null) {
                // TODO(zhangwen): we currently ignore NULL values, i.e., assuming NULLs are irrelevant for compliance.
                ValueOperand rhs = new ValueOperand(value);
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
                Operand lhs = expr2Operand.get(p1);
                for (int j = i + 1; j < variables.size(); ++j) {
                    Expr p2 = variables.get(j);
                    Operand rhs = expr2Operand.get(p2);
                    label2Expr.put(new EqualityLabel(lhs, rhs), context.mkEq(p1, p2));
                }
            }
        }

        for (Object value1 : ecs.keySet()) {
            for (Object value2 : ecs.keySet()) {
                if (!Tuple.valueLessThan(value1, value2)) {
                    continue;
                }

                ValueOperand vo1 = new ValueOperand(value1), vo2 = new ValueOperand(value2);
                Expr vExpr1 = Tuple.getExprFromObject(context, value1),
                        vExpr2 = Tuple.getExprFromObject(context, value2);
                for (Expr p1 : ecs.get(value1)) {
                    Operand o1 = expr2Operand.get(p1);
                    label2Expr.put(new LessThanLabel(o1, vo2), context.mkCustomIntLt(p1, vExpr2));
                }
                for (Expr p2 : ecs.get(value2)) {
                    Operand o2 = expr2Operand.get(p2);
                    label2Expr.put(new LessThanLabel(vo1, o2), context.mkCustomIntLt(vExpr1, p2));
                }

                for (Expr p1 : ecs.get(value1)) {
                    Operand lhs = expr2Operand.get(p1);
                    for (Expr p2 : ecs.get(value2)) {
                        Operand rhs = expr2Operand.get(p2);
                        label2Expr.put(new LessThanLabel(lhs, rhs), context.mkCustomIntLt(p1, p2));
                    }
                }
            }
        }

        return label2Expr;
    }

    // Optimization: For two operands that are always equal, remove one of them (from `ecs` & `expr2Operand`);
    // if one operand is a pk-valued expr, and add the other to `pkValuedExprs`.
    private void removeRedundantExprs(ArrayListMultimap<Object, Expr> ecs,
                                      Map<Expr, Operand> expr2Operand,
                                      Set<Expr> pkValuedExprs,
                                      Collection<BoolExpr> returnedRowExprs) {
        Solver solver = context.mkSolver(context.mkSymbol("QF_UF"));
        solver.add(returnedRowExprs.toArray(new BoolExpr[0]));

        for (Object v : ecs.keySet()) {
            HashSet<Expr> redundantExprs = new HashSet<>();
            List<Expr> variables = ecs.get(v);
            for (Expr p1 : variables) {
                Operand o1 = expr2Operand.get(p1);
                // Only look at labels of the form "query param = returned row attribute".
                if (o1.getKind() != Operand.Kind.QUERY_PARAM) {
                    continue;
                }
                QueryParamOperand qpo1 = (QueryParamOperand) o1;
                if (qpo1.isCurrentQuery()) {
                    continue;
                }

                for (Expr p2 : variables) {
                    Operand o2 = expr2Operand.get(p2);
                    if (o2.getKind() != Operand.Kind.RETURNED_ROW_ATTR) {
                        continue;
                    }
                    if (((ReturnedRowFieldOperand) o2).getQueryIdx() != qpo1.getQueryIdx()) {
                        continue;
                    }

                    long startMs = System.currentTimeMillis();
                    Status res = solver.check(context.mkNot(context.mkEq(p1, p2)));
//                    System.out.println("\t\t| removeRedundant check:\t" + (System.currentTimeMillis() - startMs));
                    if (res == Status.UNSATISFIABLE) {
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
}