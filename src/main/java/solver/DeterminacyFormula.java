package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import org.codehaus.janino.util.Producer;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public abstract class DeterminacyFormula {
    protected final Context context;
    protected final Schema schema;
    protected final Instance inst1;
    protected final Instance inst2;

    private final String preparedExprSMT;
    private final Map<String, Integer> preparedStringReplacement;
    private final Set<String> preparedIntReplacement;

    protected DeterminacyFormula(Schema schema, Function<Integer, Instance> makeInstance, BiFunction<Instance, Instance, BoolExpr> mkPreparedExpr) {
        this.schema = schema;
        this.context = schema.getContext();
        this.inst1 = makeInstance.apply(0);
        this.inst2 = makeInstance.apply(1);

        // Set prepared expr.
        Solver solver = schema.getContext().mkSolver();
        solver.add(mkPreparedExpr.apply(this.inst1, this.inst2));
        String result = solver.toString();
        HashSet<String> preparedIntReplacement = new HashSet<>();
        result = replaceInts(result, new HashSet<>(), preparedIntReplacement, false);
        HashMap<String, Integer> preparedStringReplacement = new HashMap<>();
        result = replaceStrings(result, new HashMap<>(), preparedStringReplacement, false);

        this.preparedIntReplacement = Collections.unmodifiableSet(preparedIntReplacement);
        this.preparedStringReplacement = Collections.unmodifiableMap(preparedStringReplacement);
        this.preparedExprSMT = "(declare-sort STRING 0)(declare-sort INT 0)\n(declare-fun lt (INT INT) Bool)\n(declare-fun gt (INT INT) Bool)" + result;
    }

    protected BoolExpr generateTupleCheck(QueryTrace queries) {
        List<BoolExpr> exprs = new ArrayList<>();
        for (List<QueryTraceEntry> queryTraceEntries : queries.getQueries().values()) {
            for (QueryTraceEntry queryTraceEntry : queryTraceEntries) {
                Query query = queryTraceEntry.getQuery().getSolverQuery(schema);
                Relation r1 = query.apply(inst1);
                Relation r2 = query.apply(inst2);
                if (!queryTraceEntry.getTuples().isEmpty()) {
                    List<Tuple> tuples = queryTraceEntry.getTuples().stream().map(
                            tuple -> new Tuple(schema, tuple.stream().map(
                                    v -> Tuple.getExprFromObject(context, v)
                            ))).collect(Collectors.toList());
                    exprs.add(r1.doesContain(tuples));
                    exprs.add(r2.doesContain(tuples));
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

    protected abstract BoolExpr makeFormula(QueryTrace queries);

    protected String makeFormulaSMT(QueryTrace queries) {
        return "(assert " + makeFormula(queries).toString() + ")";
    }

    public String generateSMT(QueryTrace queries) {
//        System.out.println("\t| Make SMT:");
        StringBuilder sb = new StringBuilder();
        MyZ3Context myContext = (MyZ3Context) context;
        myContext.startTrackingConsts();
        String smt = makeFormulaSMT(queries);
        myContext.stopTrackingConsts();

        for (Expr constant : myContext.getConsts()) {
            sb.append("(declare-fun ").append(constant.getSExpr()).append(" () ").append(constant.getSort().getSExpr()).append(")\n");
        }

        sb.append(smt);

        String body = sb.toString();
        body = replaceInts(body, this.preparedIntReplacement, new HashSet<>(), true);
        body = replaceStrings(body, this.preparedStringReplacement, new HashMap<>(), true);
        return this.preparedExprSMT + body;
    }

    private static String replaceInts(String smt, Set<String> existingInts, Set<String> newInts, boolean finishUp) {
        java.util.regex.Pattern pattern = Pattern.compile("\\(- (\\d+)\\)");
        Matcher matcher = pattern.matcher(smt);
        StringBuilder body1 = new StringBuilder();
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
        StringBuilder body2 = new StringBuilder();
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
        StringBuilder body = new StringBuilder();
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
