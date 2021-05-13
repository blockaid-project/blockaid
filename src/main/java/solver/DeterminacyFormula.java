package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.StringSymbol;
import com.microsoft.z3.Solver;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public abstract class DeterminacyFormula {
    protected final Context context;
    protected Schema schema;
    protected Instance inst1;
    protected Instance inst2;
    protected BoolExpr preparedExpr;

    protected String preparedExprSMT;
    protected Map<String, Integer> preparedStringReplacement = new HashMap<>();
    protected Set<String> preparedIntReplacement = new HashSet<>();

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

        String result = solver.toString();
        result = replaceInts(result, new HashSet<>(), this.preparedIntReplacement, false);
        result = replaceStrings(result, new HashMap<>(), this.preparedStringReplacement, false);

        this.preparedIntReplacement = Collections.unmodifiableSet(this.preparedIntReplacement);
        this.preparedStringReplacement = Collections.unmodifiableMap(this.preparedStringReplacement);

        this.preparedExprSMT = "(declare-sort STRING 0)(declare-sort INT 0)\n(declare-fun lt (INT INT) Bool)\n(declare-fun gt (INT INT) Bool)" + result;
    }

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

    public synchronized String generateSMT(QueryTrace queries) {
//        System.out.println("\t| Make SMT:");
        StringBuilder sb = new StringBuilder();
        synchronized (context) {
            MyZ3Context myContext = (MyZ3Context) context;
            myContext.startTrackingConsts();
            String smt = makeFormulaSMT(queries, makeFormulaConstants(queries));
            myContext.stopTrackingConsts();

            for (Expr constant : myContext.getConsts()) {
                sb.append("(declare-fun ").append(constant.getSExpr()).append(" () ").append(constant.getSort().getSExpr()).append(")\n");
            }

            sb.append(smt);
        }

        String body = sb.toString();
        body = replaceInts(body, this.preparedIntReplacement, new HashSet<>(), true);
        body = replaceStrings(body, this.preparedStringReplacement, new HashMap<>(), true);
        return this.preparedExprSMT + body;
    }

    private static String replaceInts(String smt, Set<String> existingInts, Set<String> newInts, boolean finishUp) {
        java.util.regex.Pattern pattern = Pattern.compile("\\(- (\\d+)\\)");
        Matcher matcher = pattern.matcher(smt);
        StringBuffer body1 = new StringBuffer();
        while (matcher.find()) {
            matcher.appendReplacement(body1, "");
            String s = "-" + matcher.group(1);
            if (!existingInts.contains(s)) {
                newInts.add(s);
            }
            body1.append(" int!-").append(s);
        }
        matcher.appendTail(body1);

        pattern = Pattern.compile("\\s(\\d+)");
        matcher = pattern.matcher(body1.toString());
        StringBuffer body2 = new StringBuffer();
        while (matcher.find()) {
            matcher.appendReplacement(body2, "");
            String s = matcher.group(1);
            if (!existingInts.contains(s)) {
                newInts.add(s);
            }
            body2.append(" int!").append(s);
        }
        matcher.appendTail(body2);

        StringBuilder out = new StringBuilder();
        for (String i : newInts) {
            out.append("(declare-fun int!").append(i).append(" () INT)\n");
        }
        if (finishUp) {
            out.append("(assert (distinct");
            for (String i : existingInts) { out.append(" int!").append(i); }
            for (String i : newInts) { out.append(" int!").append(i); }
            out.append("))\n");
        }
        out.append(body2);

        String transformed = out.toString();
        return transformed.replaceAll("<", "lt").replaceAll("\\(>", "(gt").replaceAll("Int", "INT");
    }

    private static String replaceStrings(String smt, Map<String, Integer> existingRep, Map<String, Integer> newRep, boolean finishUp) {
        java.util.regex.Pattern pattern = Pattern.compile("\"([^\"]*)\"");
        Matcher matcher = pattern.matcher(smt);
        StringBuffer body = new StringBuffer();
        int nextId = existingRep.size();
        while (matcher.find()) {
            matcher.appendReplacement(body, "");
            String s = matcher.group(1);
            Integer rep = existingRep.get(s);
            if (rep == null) { rep = newRep.get(s); }
            if (rep == null) {
                newRep.put(s, nextId);
                rep = nextId;
                nextId += 1;
            }
            body.append("string!").append(rep);
        }
        matcher.appendTail(body);

        StringBuilder out = new StringBuilder();
        for (Map.Entry<String, Integer> entry : newRep.entrySet()) {
            out.append("(declare-fun string!").append(entry.getValue()).append(" () STRING)");
            if (entry.getKey().length() < 10) {
                out.append("; ").append(entry.getKey());
            }
            out.append("\n");
        }

        if (finishUp) {
            out.append("(assert (distinct");
            for (int i = 0; i < existingRep.size() + newRep.size(); ++i) {
                out.append(" string!").append(i);
            }
            out.append("))\n");
        }
        out.append(body);

        return out.toString().replaceAll("String", "STRING");
    }
}
