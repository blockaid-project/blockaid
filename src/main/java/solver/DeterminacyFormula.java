package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.google.common.collect.Iterables;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;

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
        Solver solver = schema.getContext().mkSolver();
        solver.add(mkPreparedExpr.apply(this.inst1, this.inst2).toArray(new BoolExpr[0]));
        solver.add(additionalAssertion(context));
        String result = solver.toString();
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

        // Constrain constant values.
//        for (Map.Entry<String, Integer> entry : queries.getConstMap().entrySet()) {
//            StringSymbol nameSymbol = context.mkSymbol("!" + entry.getKey());
//            exprs.add(context.mkEq(
//                    context.mkConst(nameSymbol, context.getIntSort()),
//                    context.mkInt(entry.getValue())
//            ));
//        }

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
        return Iterables.concat(generateTupleCheck(queries), notContainsFormulas);
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
        MyZ3Context myContext = context;
        myContext.startTrackingConsts();
        String smt = makeFormulaSMT(queries);
        myContext.stopTrackingConsts();

        for (Expr constant : myContext.getConsts()) {
            sb.append("(declare-fun ").append(constant.getSExpr()).append(" () ").append(constant.getSort().getSExpr()).append(")\n");
        }

        sb.append(smt);

        String body = sb.toString();
        return this.preparedExprSMT + body;
    }
}
