package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.StringSymbol;
import com.microsoft.z3.Solver;

import java.util.*;
import java.util.stream.Collectors;

public abstract class DeterminacyFormula {
    protected Context context;
    protected Schema schema;
    protected Instance inst1;
    protected Instance inst2;
    protected BoolExpr preparedExpr;
    protected String preparedExprSMT;

    protected DeterminacyFormula(Context context, Schema schema, Collection<Query> views) {
        this.context = context;
        this.schema = schema;
        this.inst1 = schema.makeFreshInstance(context);
        this.inst2 = schema.makeFreshInstance(context);
        this.preparedExpr = null;
    }

    protected void setPreparedExpr(BoolExpr expr) {
        this.preparedExpr = expr;
        Solver solver = this.context.mkSolver();
        solver.add(this.preparedExpr);
        this.preparedExprSMT = solver.toString();
    }

<<<<<<< HEAD
    protected BoolExpr generateTraceConformanceExpr(QuerySequence queries) {
        List<BoolExpr> exprs = new ArrayList<>();

        // `inst1` and `inst2` must be consistent with the results of previous queries.
        for (QueryWithResult queryWithResult : queries.getTrace()) {
            Query query = queryWithResult.query.getSolverQuery(schema);
            Relation r1 = query.apply(context, inst1);
            Relation r2 = query.apply(context, inst2);
            if (queryWithResult.tuples != null) {
                List<Tuple> tuples = queryWithResult.tuples.stream().map(tuple -> new Tuple(tuple.stream().map(v -> Tuple.getExprFromObject(context, v)).toArray(Expr[]::new))).collect(Collectors.toList());
                exprs.add(r1.doesContain(context, tuples));
                exprs.add(r2.doesContain(context, tuples));
=======
    protected BoolExpr generateTupleCheck(QueryTrace queries, Expr[] constants) {
        List<BoolExpr> exprs = new ArrayList<>();
        for (List<QueryTraceEntry> queryTraceEntries : queries.getQueries().values()) {
            for (QueryTraceEntry queryTraceEntry : queryTraceEntries) {
                Query query = queryTraceEntry.getQuery().getSolverQuery(schema);
                Relation r1 = query.apply(context, inst1);
                Relation r2 = query.apply(context, inst2);
                if (!queryTraceEntry.getTuples().isEmpty()) {
                    List<Tuple> tuples = queryTraceEntry.getTuples().stream().map(tuple -> new Tuple(tuple.stream().map(v -> Tuple.getExprFromObject(context, v)).toArray(Expr[]::new))).collect(Collectors.toList());
                    exprs.add(r1.doesContain(context, tuples));
                    exprs.add(r2.doesContain(context, tuples));
                }
>>>>>>> 3fcc56d70c9285abd82711e641c08ec424e80214
            }
        }

        // Constrain constant values.
        for (Map.Entry<String, Integer> entry : queries.getConstMap().entrySet()) {
            StringSymbol nameSymbol = context.mkSymbol("!" + entry.getKey());
            exprs.add(context.mkEq(
                    context.mkConst(nameSymbol, context.getIntSort()),
                    context.mkInt(entry.getValue())
            ));
        }

        if (exprs.isEmpty()) {
            return context.mkTrue();
        }
        return context.mkAnd(exprs.toArray(new BoolExpr[0]));
    }

    protected abstract Expr[] makeFormulaConstants(QueryTrace queries);
    protected abstract BoolExpr makeFormula(QueryTrace queries, Expr[] constants);

    protected String makeFormulaSMT(QueryTrace queries, Expr[] constants) {
        return "(assert " + makeFormula(queries, constants).toString() + ")";
    }

    public Solver makeSolver(QueryTrace queries) {
        Solver solver = context.mkSolver();
        solver.add(preparedExpr);
        solver.add(makeFormula(queries, makeFormulaConstants(queries)));
        return solver;
    }

<<<<<<< HEAD
    public synchronized String generateSMT(QuerySequence queries) {
//        System.out.println("\t| Make SMT:");

        MyZ3Context myContext = (MyZ3Context) context;
        myContext.startTrackingConsts();
        BoolExpr bodyFormula = makeFormula(queries, makeFormulaConstants(queries));
        myContext.stopTrackingConsts();

//        long startTime = System.currentTimeMillis();
//        Expr[] constants = makeFormulaConstants(queries);
//        BoolExpr bodyFormula = makeFormula(queries, constants);
//        long endTime = System.currentTimeMillis();
//        System.out.println("\t\t| Make formula:\t" + (endTime - startTime));
//
//        startTime = System.currentTimeMillis();
//        Solver solver = context.mkSolver();
//        solver.add(bodyFormula);
//        endTime = System.currentTimeMillis();
//        System.out.println("\t\t| Add formula:\t" + (endTime - startTime));
//
//        startTime = System.currentTimeMillis();
//        String bodySMT = solver.toString();
//        endTime = System.currentTimeMillis();
//        System.out.println("\t\t| toString:\t" + (endTime - startTime));
//
//        startTime = System.currentTimeMillis();
//
//        StringBuilder sb = new StringBuilder();
//        sb.append(preparedExprSMT);
//
//        boolean shouldIncludeLine = true;
//        // FIXME(zhangwen): Hack-- Removing duplicate `declare-fun` commands; relies on Z3's output format.
//        for (String line : bodySMT.split("\\R")) {
//            if (line.startsWith("(")) { // Start of a new command.
//                shouldIncludeLine = true;
//                if (line.startsWith("(declare-fun")) {
//                    String name = line.split("\\s+")[1];
//                    if (declaredFuncsInPrepared.contains(name)) {
//                        shouldIncludeLine = false;
//                    }
//                }
//            }
//            if (shouldIncludeLine) {
//                sb.append(line);
//            }
//        }
//        String formulaSMT = sb.toString();
//
//        endTime = System.currentTimeMillis();
//        System.out.println("\t\t| de-dup:\t" + (endTime - startTime));
//
//        return formulaSMT;

=======
    public synchronized String generateSMT(QueryTrace queries) {
        Expr[] constants = makeFormulaConstants(queries);
>>>>>>> 3fcc56d70c9285abd82711e641c08ec424e80214
        StringBuilder stringBuilder = new StringBuilder();
        for (Expr constant : myContext.getConsts()) {
            stringBuilder.append("(declare-fun ").append(constant.getSExpr()).append(" () ").append(constant.getSort().getSExpr()).append(")\n");
        }
        stringBuilder.append(this.preparedExprSMT);
<<<<<<< HEAD
        stringBuilder.append("(assert ").append(bodyFormula).append(")");
=======
        stringBuilder.append(makeFormulaSMT(queries, constants));
>>>>>>> 3fcc56d70c9285abd82711e641c08ec424e80214
        return stringBuilder.toString();
    }
}
