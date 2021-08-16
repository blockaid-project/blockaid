package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.google.common.collect.Iterables;
import com.microsoft.z3.*;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public abstract class DeterminacyFormula {
    protected final MyZ3Context context;
    protected final Schema schema;
    protected final Instance inst1;
    protected final Instance inst2;

    private final String preparedExprSMT;

    protected DeterminacyFormula(Schema schema, Function<Integer, Instance> makeInstance,
                                 BiFunction<Instance, Instance, List<BoolExpr>> mkPreparedExpr) {
        this.schema = schema;
        this.context = schema.getContext();
        this.inst1 = makeInstance.apply(0);
        this.inst2 = makeInstance.apply(1);

        // Set prepared expr.
        final long startTime = System.currentTimeMillis();
        Solver solver = schema.getContext().mkRawSolver();
        solver.add(mkPreparedExpr.apply(this.inst1, this.inst2).toArray(new BoolExpr[0]));
        solver.add(additionalAssertion(context));
        String result = solver.toString();
        // Remove the custom sorts from preamble -- we add them back when generating the rest of the formula,
        // because here, sorts that are not used in the preamble but are used later on won't be declared.
        result = result.replaceAll("\\(declare-sort CS![A-Z]+ 0\\)|\\(declare-fun CS![A-Z]+!\\d+ \\(\\) CS![A-Z]+\\)", "");
        System.out.println("set prepared expr " + getClass().getName() + ":" + (System.currentTimeMillis() - startTime));
        this.preparedExprSMT = result;
    }

    protected BoolExpr additionalAssertion(MyZ3Context context) {
        return context.mkTrue();
    }

    protected Iterable<BoolExpr> generateTupleCheck(QueryTrace queries) {
        List<BoolExpr> exprs = new ArrayList<>();
        for (QueryTraceEntry queryTraceEntry : queries.getAllEntries()) {
            Query query = queryTraceEntry.getQuery().getSolverQuery(schema);
            Relation r1 = query.apply(inst1);
            Relation r2 = query.apply(inst2);
            List<Tuple> tuples = queryTraceEntry.getTuplesStream().map(
                    tuple -> new Tuple(schema, tuple.stream().map(
                            v -> Tuple.getExprFromObject(context, v)
                    ))).collect(Collectors.toList());
            if (!tuples.isEmpty()) {
                exprs.add(r1.doesContain(tuples));
                exprs.add(r2.doesContain(tuples));
            }
        }
        return exprs;
    }

    protected Iterable<BoolExpr> generateConstantCheck(QueryTrace queries) {
        List<BoolExpr> exprs = new ArrayList<>();
        // Constrain constant values.
        for (Map.Entry<String, Integer> entry : queries.getConstMap().entrySet()) {
            StringSymbol nameSymbol = context.mkSymbol("!" + entry.getKey());
            exprs.add(context.mkEq(
                    context.mkConst(nameSymbol, context.getCustomIntSort()),
                    context.mkCustomInt(entry.getValue())
            ));
        }

        return exprs;
    }

    public Iterable<BoolExpr> makeFormula(QueryTrace queries) {
        /* Both regular and fast unsat share this formula form -- by symmetry, we can write Q(D1) != Q(D2) using
        "not contained in". */
        Query query = queries.getCurrentQuery().getQuery().getSolverQuery(schema);
        Tuple extHeadTup = query.makeFreshHead();
        List<BoolExpr> notContainsFormulas = List.of(
                query.doesContain(inst1, extHeadTup),
                context.mkNot(query.doesContain(inst2, extHeadTup)));
        return Iterables.concat(generateTupleCheck(queries), generateConstantCheck(queries), notContainsFormulas);
    }

    protected String makeFormulaSMT(QueryTrace queries) {
        StringBuilder sb = new StringBuilder();
        for (BoolExpr formula : makeFormula(queries)) {
            sb.append("(assert ").append(formula).append(")\n");
        }
        return sb.toString();
    }

    public String generateSMT(QueryTrace queries) {
        StringBuilder sb = new StringBuilder();
        context.startTrackingConsts();
        String smt = makeFormulaSMT(queries);
        context.stopTrackingConsts();

        for (Expr constant : context.getConsts()) {
            if (!constant.getSExpr().startsWith("CS!")) {
                sb.append("(declare-fun ").append(constant.getSExpr()).append(" () ").append(constant.getSort().getSExpr()).append(")\n");
            }
        }

        sb.append(smt);

        // only used to generate declarations and assertions for sorts
        String header = context.prepareSortDeclaration();
        String body = sb.toString();
        return header + this.preparedExprSMT + body + "(check-sat)";
    }
}
