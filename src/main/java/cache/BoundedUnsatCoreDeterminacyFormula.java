package cache;

import cache.labels.*;
import cache.trace.QueryTraceEntry;
import cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.*;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import policy_checker.Policy;
import solver.*;
import sql.PrivacyQuery;
import sql.PrivacyQuerySelect;
import sql.SchemaPlusWithKey;

import java.util.*;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkState;

public class BoundedUnsatCoreDeterminacyFormula extends BoundedDeterminacyFormula {
    public enum LabelOption {
        RETURNED_ROWS_ONLY,
        PARAM_LABELS_ONLY, // FIXME(zhangwen): rename?
    }

    private final ImmutableSet<String> relevantAttributes;

//    public static BoundedUnsatCoreDeterminacyFormula create(
//            Schema schema, Collection<Policy> policies,
//            Collection<Query> views, Map<String, Integer> bounds
//    ) {
//        long startTime = System.currentTimeMillis();
//        CountingBoundEstimator cbe = new CountingBoundEstimator();
//        BoundEstimator boundEstimator = new UnsatCoreBoundEstimator(cbe);
//        System.out.println("\t\t| Compute bounds:\t" + (System.currentTimeMillis() - startTime) + "\t" + bounds);
//
//        // FIXME(zhangwen): we can't actually constrain the tables to contain known rows, because then we wouldn't be
//        //  able to tell the difference made by removing a previous query.
//        ListMultimap<String, Map<String, Object>> knownRows = null;
////        if (option == LabelOption.FIX_RETURNED_ROWS) {
////            startTime = System.currentTimeMillis();
////            knownRows = computeKnownRows(schema, trace);
////            System.out.println("\t\t| Known rows:\t" + knownRows);
////        }
//        BoundedUnsatCoreDeterminacyFormula f =
//                new BoundedUnsatCoreDeterminacyFormula(schema, policies, views, bounds, knownRows);
//        System.out.println("\t\t| Formula constructor:\t" + (System.currentTimeMillis() - startTime));
//        return f;
//    }

    private static class TableColumnPair {
        public final String table;
        public final Object value;

        public TableColumnPair(String table, Object value) {
            this.table = table;
            this.value = value;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            TableColumnPair that = (TableColumnPair) o;
            return table.equals(that.table) && value.equals(that.value);
        }

        @Override
        public int hashCode() {
            return Objects.hash(table, value);
        }
    }

    private static ListMultimap<String, Map<String, Object>> computeKnownRows(
            Schema schema, UnmodifiableLinearQueryTrace trace) {
        SchemaPlusWithKey rawSchema = schema.getRawSchema();
        Map<String, String> tableName2PkName = new HashMap<>();
        for (String tableName : schema.getRelationNames()) {
            Optional<ImmutableList<String>> oPkColumns = rawSchema.getPrimaryKeyColumns(tableName);
            if (oPkColumns.isEmpty()) {
                continue;
            }

            // Currently, only supports tables with exactly one primary key column.
            ImmutableList<String> pkColumns = oPkColumns.get();
            if (pkColumns.size() != 1) {
                continue;
            }
            tableName2PkName.put(tableName, Iterables.getOnlyElement(pkColumns));
        }

        Map<TableColumnPair, Map<String, Object>> tablePk2Rows = new HashMap<>();
        for (QueryTraceEntry qte : trace.getAllEntries()) {
            if (!qte.hasTuples()) {
                continue;
            }
            List<List<Object>> tuples = qte.getTuples();
            // TODO(zhangwen): add a method to query that returns the number of columns.
            int numColumns = tuples.get(0).size();

            PrivacyQuery pq = qte.getQuery();
            if (!(pq instanceof PrivacyQuerySelect)) {
                continue;
            }
            PrivacyQuerySelect pqs = (PrivacyQuerySelect) pq;

            // Maps table name to the column index of its primary key, if returned by the query.
            List<String[]> columns = new ArrayList<>();
            Map<String, Integer> tableName2PkIdx = new HashMap<>();
            for (int colIdx = 0; colIdx < numColumns; ++colIdx) {
                Set<String> columnNames = pqs.getProjectColumnsByIdx(colIdx);
                checkState(columnNames.size() == 1,
                        "a SELECT query should have exactly one column name per index, got: " + columnNames);
                String columnName = Iterables.getOnlyElement(columnNames);

                String[] parts = columnName.split("\\.", 2);
                String tableName = parts[0];
                // FIXME(zhangwen): assumes that no table is aliased to another table's name.
                if (parts[1].equals(tableName2PkName.get(tableName))) {
                    checkState(!tableName2PkIdx.containsKey(tableName));
                    tableName2PkIdx.put(tableName, colIdx);
                }

                columns.add(parts);
            }

            for (List<Object> tup : tuples) {
                Map<String, TableColumnPair> tableName2PkValue = new HashMap<>();
                for (Map.Entry<String, Integer> e : tableName2PkIdx.entrySet()) {
                    String tableName = e.getKey();
                    tableName2PkValue.put(tableName, new TableColumnPair(tableName, tup.get(e.getValue())));
                }

                for (int colIdx = 0; colIdx < tup.size(); ++colIdx) {
                    String[] parts = columns.get(colIdx);
                    Object pkValue = tableName2PkValue.get(parts[0]);
                    if (pkValue == null) {
                        continue;
                    }
                    TableColumnPair tcp = tableName2PkValue.get(parts[0]);
                    if (tcp == null) {
                        continue;
                    }
                    Map<String, Object> knownRow = tablePk2Rows.computeIfAbsent(tcp, k -> new HashMap<>());
                    if (knownRow.containsKey(parts[1])) {
                        checkState(Objects.equals(knownRow.get(parts[1]), tup.get(colIdx)));
                    } else {
                        knownRow.put(parts[1], tup.get(colIdx));
                    }
                }
            }
        }

        ListMultimap<String, Map<String, Object>> knownRows = ArrayListMultimap.create();
        for (Map.Entry<TableColumnPair, Map<String, Object>> e : tablePk2Rows.entrySet()) {
            knownRows.put(e.getKey().table, e.getValue());
        }
        return knownRows;
    }

    public BoundedUnsatCoreDeterminacyFormula(Schema schema, Collection<Policy> policies, Collection<Query> views,
                                               Map<String, Integer> bounds,
                                               ListMultimap<String, Map<String, Object>> table2KnownRows) {
        super(schema, views, bounds, true, TextOption.NO_TEXT, table2KnownRows);
        // TODO(zhangwen): don't compute this all the time.
        this.relevantAttributes = Stream.concat(
                policies.stream().flatMap(policy -> policy.getNormalizedThetaColumns().stream()),
                schema.getDependencies().stream().flatMap(c -> c.getRelevantColumns().stream())
        ).collect(ImmutableSet.toImmutableSet());
    }

    private Map<Label, BoolExpr> makeLabeledExprsRR(UnmodifiableLinearQueryTrace trace) {
        Map<Label, BoolExpr> label2Expr = new HashMap<>();
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
                Label l = new ReturnedRowLabel(queryIdx, rowIdx);
                label2Expr.put(l, context.mkAnd(r1.doesContainExpr(tuple)));
            }
        }
        return label2Expr;
    }

    public Map<Label, BoolExpr> makeLabeledExprs(UnmodifiableLinearQueryTrace trace, LabelOption option) {
        if (option == LabelOption.RETURNED_ROWS_ONLY) {
            return makeLabeledExprsRR(trace);
        }

        checkState(option == LabelOption.PARAM_LABELS_ONLY);
        MyZ3Context context = schema.getContext();
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

            Relation r1 = q.apply(inst1);
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
//        System.out.println("\t\t| removeRedundantExprs:\t" + (System.currentTimeMillis() - startTime));

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

    // Makes formula that is not under consideration for unsat core.
    public Iterable<BoolExpr> makeBackgroundFormulas(UnmodifiableLinearQueryTrace trace, LabelOption option) {
        ArrayList<BoolExpr> formulas = new ArrayList<>(preamble);

        if (option == LabelOption.RETURNED_ROWS_ONLY) {
            Iterables.addAll(formulas, generateConstantCheck(trace));
            Iterables.addAll(formulas, generateNotContains(trace));
        } else {
            checkState(option == LabelOption.PARAM_LABELS_ONLY, "illegal option: " + option);
            Query query = trace.getCurrentQuery().getQuery().getSolverQuery(schema, "cq", 0);
            Tuple extHeadTup = query.makeFreshHead();
            Iterables.addAll(formulas, query.apply(inst1).doesContainExpr(extHeadTup));
            formulas.add(context.mkNot(context.mkAnd(query.apply(inst2).doesContainExpr(extHeadTup))));
        }
        return formulas;
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

    @Deprecated
    @Override
    public Iterable<BoolExpr> makeCompleteFormula(UnmodifiableLinearQueryTrace queries) {
        throw new UnsupportedOperationException();
    }

    @Deprecated
    @Override
    public Iterable<BoolExpr> makeBodyFormula(UnmodifiableLinearQueryTrace queries) {
        throw new UnsupportedOperationException();
    }

    @Deprecated
    @Override
    public String generateSMT(UnmodifiableLinearQueryTrace queries) {
        throw new UnsupportedOperationException();
    }
}
