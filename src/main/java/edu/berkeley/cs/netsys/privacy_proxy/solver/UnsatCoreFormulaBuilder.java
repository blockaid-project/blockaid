package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.*;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.*;
import edu.berkeley.cs.netsys.privacy_proxy.util.LogLevel;
import edu.berkeley.cs.netsys.privacy_proxy.util.Logger;
import edu.berkeley.cs.netsys.privacy_proxy.util.TerminalColor;
import org.checkerframework.checker.nullness.qual.Nullable;

import java.util.*;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkState;

public class UnsatCoreFormulaBuilder<C extends Z3ContextWrapper<?, ?, ?, ?>, I extends Instance<C>> {
    private final DeterminacyFormula<C, I> baseFormula;
    private final ImmutableSet<String> relevantAttributes;

    // Shorthands.
    private final Schema<C> schema;
    private final C context;

    public enum Option {
        NO_PREAMBLE,
        NO_REMOVE_REDUNDANT,
        NO_MARK_BG,
    }

    public UnsatCoreFormulaBuilder(DeterminacyFormula<C, I> baseFormula, Collection<Policy> policies) {
        this.baseFormula = baseFormula;
        this.schema = baseFormula.schema;
        this.context = baseFormula.context;

        this.relevantAttributes = Stream.concat(
                policies.stream().flatMap(policy -> policy.getNormalizedThetaColumns().stream()),
                schema.getDependencies().stream().flatMap(c -> c.getRelevantColumns().stream())
        ).collect(ImmutableSet.toImmutableSet());
    }

    public static record Formulas<L, BL>(
            ImmutableMap<L, BoolExpr> labeledExprs,
            ImmutableList<LabeledBoolExpr<BL>> background // Formula that is not under consideration for unsat core.
    ) {}

    public Formulas<ReturnedRowLabel, PreambleLabel> buildReturnedRowsOnly(UnmodifiableLinearQueryTrace trace,
                                                                           EnumSet<Option> options) {
        ImmutableMap<ReturnedRowLabel, BoolExpr> labeledExprs = makeLabeledExprsRR(trace);

        Stream<LabeledBoolExpr<PreambleLabel>> preambleBgStream =
                baseFormula.preamble.entrySet().stream()
                        .map(entry -> {
                                    BoolExpr formula = context.mkAnd(entry.getValue());
                                    if (options.contains(Option.NO_MARK_BG)) {
                                        return LabeledBoolExpr.makeUnlabeled(formula);
                                    } else {
                                        return new LabeledBoolExpr<>(formula, entry.getKey());
                                    }
                                });
        Stream<LabeledBoolExpr<PreambleLabel>> otherBgStream =
                Streams.concat(
                        Streams.stream(baseFormula.generateConstantCheck(trace)),
                        Streams.stream(baseFormula.generateNotContains(trace))
                ).map(LabeledBoolExpr::makeUnlabeled);

        ImmutableList<LabeledBoolExpr<PreambleLabel>> background = Streams.concat(preambleBgStream, otherBgStream)
                .collect(ImmutableList.toImmutableList());
        return new Formulas<>(labeledExprs, background);
    }

    public Formulas<Label, PreambleLabel> buildParamRelationsOnly(UnmodifiableLinearQueryTrace trace) {
        return buildParamRelationsOnly(trace, EnumSet.noneOf(Option.class));
    }

    /**
     * Builds unsat core formulas assuming the entire trace is present, i.e., returned-row labels count as background.
     * @param trace the trace to generate formulas for.
     * @param options options for the formula.
     * @return unsat core formulas.
     */
    public Formulas<Label, PreambleLabel> buildParamRelationsOnly(UnmodifiableLinearQueryTrace trace,
                                                                  EnumSet<Option> options) {
        Map<Label, BoolExpr> allLabeledExprs = makeLabeledExprsAll(trace, options);
        ImmutableList.Builder<LabeledBoolExpr<PreambleLabel>> bgBuilder = ImmutableList.builder();

        if (!options.contains(Option.NO_PREAMBLE)) {
            for (var entry : baseFormula.preamble.entrySet()) {
                BoolExpr formula = context.mkAnd(entry.getValue());
                bgBuilder.add(
                        options.contains(Option.NO_MARK_BG) ? LabeledBoolExpr.makeUnlabeled(formula)
                                : new LabeledBoolExpr<>(formula, entry.getKey())
                );
            }
        }
        Query<C> query = trace.getCurrentQuery().getQuery().getSolverQuery(schema, "cq", 0);

        // Since we're param labels-only, add returned-row labels to background and exclude them from `labeledExprs`.
        ImmutableMap.Builder<Label, BoolExpr> labeledExprsBuilder = new ImmutableMap.Builder<>();
        for (Map.Entry<Label, BoolExpr> entry : allLabeledExprs.entrySet()) {
            if (entry.getKey().getKind() == Label.Kind.RETURNED_ROW) {
                bgBuilder.add(LabeledBoolExpr.makeUnlabeled(entry.getValue()));
            } else {
                labeledExprsBuilder.put(entry);
            }
        }

        Iterable<BoolExpr> negatedConsequence = baseFormula.generateNotContains(query);
        bgBuilder.add(LabeledBoolExpr.makeUnlabeled(context.mkAnd(negatedConsequence)));

        // TODO(zhangwen): existentially quantify the database table variables so that they don't appear in the model.
        //  The code below doesn't work because the labeled exprs also reference the quantified variables.
//        if (baseFormula instanceof BoundedDeterminacyFormula<C> bdf) {
//            BoolExpr quantifiedBackground = context.myMkExists(bdf.getAllDbVars(), context.mkAnd(background));
//            background = ImmutableList.of(quantifiedBackground);
//        }

        return new Formulas<>(labeledExprsBuilder.build(), bgBuilder.build());
    }

    // Once again, assumes the entire trace is present.
    public String buildValidateParamRelationsOnlySMT(UnmodifiableLinearQueryTrace trace,
                                                     Set<Label> labels,
                                                     @Nullable Set<PreambleLabel> preambleLabels) {
        if (preambleLabels == null) {
            preambleLabels = baseFormula.computeRelevantPreambleLabels(trace);
        }
        Formulas<Label, PreambleLabel> fs = buildParamRelationsOnly(
                trace, EnumSet.of(Option.NO_PREAMBLE, Option.NO_REMOVE_REDUNDANT, Option.NO_MARK_BG));
        return baseFormula.generateSMT(
            // Don't include the preamble -- the `generateSMT` automatically.
            Streams.concat(
                    // The entire background of `fs` is unlabeled.
                    fs.background().stream().map(LabeledBoolExpr::expr),
                    Maps.filterKeys(fs.labeledExprs(), labels::contains).values().stream()
            ), preambleLabels);
    }

    private ImmutableMap<ReturnedRowLabel, BoolExpr> makeLabeledExprsRR(UnmodifiableLinearQueryTrace trace) {
        ImmutableMap.Builder<ReturnedRowLabel, BoolExpr> label2Expr = new ImmutableMap.Builder<>();
        List<QueryTraceEntry> allEntries = trace.getAllEntries();
        for (int queryIdx = 0; queryIdx < allEntries.size(); ++queryIdx) {
            QueryTraceEntry qte = allEntries.get(queryIdx);
            if (!qte.hasTuples()) {
                continue;
            }
            Query<C> query = qte.getQuery().getSolverQuery(schema);
            Relation<C> r1 = query.apply(baseFormula.inst1);
            List<Tuple<C>> tuples = DeterminacyFormula.getTupleObjects(qte, schema);

            for (int rowIdx = 0; rowIdx < tuples.size(); ++rowIdx) {
                Tuple<C> tuple = tuples.get(rowIdx);
                ReturnedRowLabel l = new ReturnedRowLabel(queryIdx, rowIdx);
                label2Expr.put(l, context.mkAnd(r1.doesContainExpr(tuple)));
            }
        }
        return label2Expr.build();
    }

    private Map<Label, BoolExpr> makeLabeledExprsAll(UnmodifiableLinearQueryTrace trace, EnumSet<Option> options) {
        QueryTraceEntry lastEntry = trace.getCurrentQuery();
        ListMultimap<Object, Expr<?>> ecs = ArrayListMultimap.create(); // Value -> constants that equal that value.

        Map<Expr<?>, Operand> expr2Operand = new HashMap<>();
        Map<Label, BoolExpr> label2Expr = new HashMap<>();

        List<QueryTraceEntry> allEntries = trace.getAllEntries();
        Set<Expr<?>> pkValuedExprs = new HashSet<>();
        for (int queryIdx = 0; queryIdx < allEntries.size(); ++queryIdx) {
            QueryTraceEntry e = allEntries.get(queryIdx);
            boolean isCurrentQuery = e == lastEntry;
            String qPrefix = (isCurrentQuery? "cq" : ("q" + queryIdx));
            Query<C> q = e.getQuery().getSolverQuery(schema, qPrefix, 0);

            if (!e.hasTuples() && !isCurrentQuery) {
                // Discard this query -- it has no returned rows, and it is not the query being checked.
                continue;
            }

            List<Object> paramValues = e.getQuery().parameters;
            int numParams = paramValues.size();
            for (int paramIdx = 0; paramIdx < numParams; ++paramIdx) {
                Expr<?> paramExpr = context.mkConst(
                        // TODO(zhangwen): this naming scheme has to match that in `ParsedPSJ`, which is error-prone.
                        "!" + qPrefix + "!" + paramIdx,
                        context.getSortForValue(paramValues.get(paramIdx)));
                Object v = paramValues.get(paramIdx);
                checkState(!expr2Operand.containsKey(paramExpr));
                expr2Operand.put(paramExpr, new QueryParamOperand(queryIdx, isCurrentQuery, paramIdx));
                ecs.put(v, paramExpr);
            }

            if (!e.hasTuples()) {
                continue;
            }

            Relation<C> r1 = q.apply(baseFormula.inst1);
            List<List<Object>> rows = e.getTuples();

            ImmutableSet<String> pkValuedColumns = schema.getRawSchema().getPkValuedColumns();

            for (int rowIdx = 0; rowIdx < rows.size(); ++rowIdx) {
                List<Object> tuple = rows.get(rowIdx);
                String tupPrefix = "!" + qPrefix + "_tup" + rowIdx;

                Tuple<C> head = q.makeHead(colIdx -> tupPrefix + "_col" + colIdx);
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
                    Expr<?> attrExpr = head.get(attrIdx);
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

        for (Map.Entry<String, Object> e : trace.getConstMap().entrySet()) {
            // FIXME(zhangwen): currently assumes that the concrete value of constant is irrelevant.
            // TODO(zhangwen): should put const naming scheme in one place.
            String name = e.getKey();
            Object value = e.getValue();
            Expr<?> constExpr = context.mkConst("!" + name, context.getSortForValue(value));
            expr2Operand.put(constExpr, new ContextConstantOperand(name));
            ecs.put(value, constExpr);
        }

        if (!options.contains(Option.NO_REMOVE_REDUNDANT)) {
            long startNs = System.nanoTime();
            removeRedundantExprs(
                    ecs,
                    expr2Operand,
                    pkValuedExprs,
                    Maps.filterKeys(label2Expr, l -> l.getKind() == Label.Kind.RETURNED_ROW).values()
            );
            System.out.println("\t\t| removeRedundantExprs:\t" + (System.nanoTime() - startNs) / 1000000);
        }

//        for (Object value : ecs.keySet()) {
//            List<Expr> variables = ecs.get(value);
//            System.out.println(value + ":\t" + variables.size() + "\t" + variables);
//        }

        for (Object value : ecs.keySet()) {
            List<Expr<?>> variables = ecs.get(value);

            // Generate equalities of the form: variable = value.
            Expr<?> vExpr = context.getExprForValue(value);
            if (vExpr != null) {
                // TODO(zhangwen): we currently ignore NULL values, i.e., assuming NULLs are irrelevant for compliance.
                ValueOperand rhs = new ValueOperand(value);
                for (Expr<?> p : variables) {
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
                Expr<?> p1 = variables.get(i);
                Operand lhs = expr2Operand.get(p1);
                for (int j = i + 1; j < variables.size(); ++j) {
                    Expr<?> p2 = variables.get(j);
                    Operand rhs = expr2Operand.get(p2);
                    // Again, we require that `p1` and `p2` are not null.
                    label2Expr.put(new EqualityLabel(lhs, rhs), context.mkSqlEqTrue(p1, p2));
                }
            }
        }

        for (Object value1 : ecs.keySet()) {
            for (Object value2 : ecs.keySet()) {
                if (!Tuple.valueLessThan(value1, value2)) {
                    continue;
                }

                ValueOperand vo1 = new ValueOperand(value1), vo2 = new ValueOperand(value2);
                Expr<?> vExpr1 = context.getExprForValue(value1), vExpr2 = context.getExprForValue(value2);
                for (Expr<?> p1 : ecs.get(value1)) {
                    Operand o1 = expr2Operand.get(p1);
                    label2Expr.put(new LessThanLabel(o1, vo2), context.mkCustomIntLtTrue(p1, vExpr2));
                }
                for (Expr<?> p2 : ecs.get(value2)) {
                    Operand o2 = expr2Operand.get(p2);
                    label2Expr.put(new LessThanLabel(vo1, o2), context.mkCustomIntLtTrue(vExpr1, p2));
                }

                for (Expr<?> p1 : ecs.get(value1)) {
                    Operand lhs = expr2Operand.get(p1);
                    for (Expr<?> p2 : ecs.get(value2)) {
                        Operand rhs = expr2Operand.get(p2);
                        label2Expr.put(new LessThanLabel(lhs, rhs), context.mkCustomIntLtTrue(p1, p2));
                    }
                }
            }
        }

        return label2Expr;
    }

    // Optimization: For two operands that are always equal, remove one of them (from `ecs` & `expr2Operand`);
    // if one operand is a pk-valued expr, and add the other to `pkValuedExprs`.
    private void removeRedundantExprs(Multimap<Object, Expr<?>> ecs,
                                      Map<Expr<?>, Operand> expr2Operand,
                                      Set<Expr<?>> pkValuedExprs,
                                      Collection<BoolExpr> returnedRowExprs) {
        Solver solver = context.mkQfSolver();
        solver.add(returnedRowExprs.toArray(new BoolExpr[0]));

        for (Object v : ecs.keySet()) {
            HashSet<Expr<?>> redundantExprs = new HashSet<>();
            Collection<Expr<?>> variables = ecs.get(v);
            for (Expr<?> p1 : variables) {
                Operand o1 = expr2Operand.get(p1);
                // Only look at labels of the form "query param = returned row attribute".
                if (o1.getKind() != Operand.Kind.QUERY_PARAM) {
                    continue;
                }
                QueryParamOperand qpo1 = (QueryParamOperand) o1;
                if (qpo1.isCurrentQuery()) {
                    continue;
                }

                for (Expr<?> p2 : variables) {
                    Operand o2 = expr2Operand.get(p2);
                    if (o2.getKind() != Operand.Kind.RETURNED_ROW_ATTR) {
                        continue;
                    }
                    if (((ReturnedRowFieldOperand) o2).queryIdx() != qpo1.queryIdx()) {
                        continue;
                    }

                    Status res = solver.check(context.mkNot(context.mkEq(p1, p2)));
                    if (res == Status.UNSATISFIABLE) {
                        // Keep the query param, toss the returned row attribute.
                        Logger.printStylizedMessage("removeRedundantExprs:\t" + o1 + " == " + o2,
                                TerminalColor.ANSI_GREEN_BACKGROUND + TerminalColor.ANSI_BLACK,
                                LogLevel.VERBOSE);
                        redundantExprs.add(p2);
                        if (pkValuedExprs.contains(p2)) {
                            pkValuedExprs.add(p1);
                        }
                    } else {
                        checkState(res == Status.SATISFIABLE,
                                "removeRedundant solver failure: " + res);
                        Logger.printStylizedMessage(() -> {
                            Model m = solver.getModel();
                            return "removeRedundantExprs:\t" + o1 + " != " + o2 + "\t" + m.eval(p1, false) + ", " + m.eval(p2, false);
                        }, TerminalColor.ANSI_RED_BACKGROUND, LogLevel.VERBOSE);
                    }
                }
            }

            variables.removeAll(redundantExprs);
            expr2Operand.keySet().removeAll(redundantExprs);
        }
    }
}
