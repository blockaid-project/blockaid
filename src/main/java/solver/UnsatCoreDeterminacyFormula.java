package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.microsoft.z3.*;
import policy_checker.Policy;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class UnsatCoreDeterminacyFormula extends DeterminacyFormula {
    private final boolean unnamedEquality;
    private final boolean eliminateIrrelevant;
    private final Set<String> relevantAttributes;

    public UnsatCoreDeterminacyFormula(Context context, Schema schema, Collection<Policy> policies, Collection<Query> views, boolean unnamedEquality, boolean eliminateIrrelevant) {
        super(context, schema, views);

        List<BoolExpr> clauses = new ArrayList<>();
        if (inst1.constraint != null) {
            clauses.add(inst1.constraint);
        }
        if (inst2.constraint != null) {
            clauses.add(inst2.constraint);
        }
        assert views.size() > 0;
        for (Query v : views) {
            clauses.add(v.apply(context, inst1).equalsExpr(context, v.apply(context, inst2)));
        }
        setPreparedExpr(context.mkAnd(clauses.toArray(new BoolExpr[0])));
        this.unnamedEquality = unnamedEquality;
        this.eliminateIrrelevant = eliminateIrrelevant;
        this.relevantAttributes = new HashSet<>();

        for (Policy policy : policies) {
            this.relevantAttributes.addAll(policy.getThetaColumns());
        }
    }

    private Map<Object, Integer> assertionMap = null;
    public Map<Object, Integer> getAssertionMap() {
        return assertionMap;
    }

    private String generateAssertions(QueryTrace queries, Expr[] constants) {
        Map<String, BoolExpr> exprs = new HashMap<>();

        int constantsOffset = 0;
        int queryNumber = 0;
        Map<Object, Set<Expr>> equalitySets = new HashMap<>();
        for (List<QueryTraceEntry> queryTraceEntries : queries.getQueries().values()) {
            for (QueryTraceEntry queryTraceEntry : queryTraceEntries) {
                String prefix = (queryTraceEntry == queries.getCurrentQuery() ? "cq_p" : ("q_p!" + queryNumber));
                Query query = queryTraceEntry.getQuery().getSolverQuery(schema, prefix, 0);

                List<String> paramNames = queryTraceEntry.getQuery().paramNames;
                Object[] parameters = queryTraceEntry.getQuery().parameters;
                Tuple paramConstants = new Tuple(Arrays.copyOfRange(constants, constantsOffset, constantsOffset + parameters.length));
                constantsOffset += parameters.length;

                Relation r1 = query.apply(context, inst1);
                Relation r2 = query.apply(context, inst2);
                if (!queryTraceEntry.getTuples().isEmpty() || queryTraceEntry == queries.getCurrentQuery()) {
                    for (int i = 0; i < parameters.length; ++i) {
                        if (paramNames.get(i).equals("?")) {
                            if (!equalitySets.containsKey(parameters[i])) {
                                // these should be linked to the query assertions since that's the only place where the
                                // constants are even used, except for the current query but that's special cased elsewhere
                                exprs.put("a_pv!" + queryNumber + "!" + i, context.mkEq(paramConstants.get(i), Tuple.getExprFromObject(context, parameters[i])));
                                equalitySets.put(parameters[i], new HashSet<>());
                            }
                            equalitySets.get(parameters[i]).add(paramConstants.get(i));
                        }
                    }
                }

                if (!queryTraceEntry.getTuples().isEmpty()) {
                    int numAttrs = query.headTypes().length;

                    List<Tuple> tupleConstants = new ArrayList<>();
                    List<String> attributeNames = queryTraceEntry.getQuery().getProjectColumns();
                    int attrNumber = 0;
                    for (List<Object> tuple : queryTraceEntry.getTuples()) {
                        Tuple tupleConstant = new Tuple(Arrays.copyOfRange(constants, constantsOffset, constantsOffset + numAttrs));
                        tupleConstants.add(tupleConstant);
                        for (int i = 0; i < tuple.size(); ++i) {
                            if (!eliminateIrrelevant || relevantAttributes.contains(attributeNames.get(i))) {
                                if (!equalitySets.containsKey(tuple.get(i))) {
                                    exprs.put("a_v!" + queryNumber + "!" + attrNumber, context.mkEq(tupleConstant.get(i), Tuple.getExprFromObject(context, tuple.get(i))));
                                    equalitySets.put(tuple.get(i), new HashSet<>());
                                }
                                equalitySets.get(tuple.get(i)).add(tupleConstant.get(i));
                            }

                            ++attrNumber;
                        }
                        constantsOffset += numAttrs;
                    }

                    exprs.put("a_q!" + queryNumber, context.mkAnd(r1.doesContain(context, tupleConstants), r2.doesContain(context, tupleConstants)));
                }

                ++queryNumber;
            }
        }

        this.assertionMap = new HashMap<>();
        int assertionNum = 0;
        for (Map.Entry<Object, Set<Expr>> entry : equalitySets.entrySet()) {
            if (entry.getValue().size() < 2) {
                continue;
            }
            boolean hasParameter = false;
            for (Expr s : entry.getValue()) {
                if (s.getSExpr().contains("p!")) {
                    hasParameter = true;
                    break;
                }
            }
            if (hasParameter) {
                List<BoolExpr> subexprs = new ArrayList<>();
                Iterator<Expr> iter = entry.getValue().iterator();
                Expr first = iter.next();
                while (iter.hasNext()) {
                    subexprs.add(context.mkEq(first, iter.next()));
                }
                exprs.put("a_e!" + assertionNum, context.mkAnd(subexprs.toArray(new BoolExpr[0])));
                this.assertionMap.put(entry.getKey(), assertionNum);
                ++assertionNum;
            }
        }

        StringBuilder out = new StringBuilder();
        for (Map.Entry<String, BoolExpr> expr : exprs.entrySet()) {
            if (unnamedEquality && expr.getKey().startsWith("a_e!")) {
                out.append("(assert ").append(expr.getValue().toString()).append(")\n");
            } else {
                out.append("(assert (! ").append(expr.getValue().toString()).append(" :named ").append(expr.getKey()).append("))\n");
            }
        }
        return out.toString();
    }

    @Override
    public Solver makeSolver(QueryTrace queries) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Expr[] makeFormulaConstants(QueryTrace queries) {
        List<Expr> exprs = new ArrayList<>();
        int queryNumber = 0;
        for (List<QueryTraceEntry> queryTraceEntries : queries.getQueries().values()) {
            for (QueryTraceEntry queryTraceEntry : queryTraceEntries) {
                String prefix = (queryTraceEntry == queries.getCurrentQuery() ? "cq_p" : ("q_p!" + queryNumber));
                Object[] parameters = queryTraceEntry.getQuery().parameters;
                for (int i = 0; i < parameters.length; ++i) {
                    exprs.add(context.mkConst("!" + prefix + "!" + i, Tuple.getSortFromObject(context, parameters[i])));
                }
                Query query = queryTraceEntry.getQuery().getSolverQuery(schema);
                if (!queryTraceEntry.getTuples().isEmpty()) {
                    Sort[] headTypes = query.headTypes();

                    for (int i = 0, numTuples = queryTraceEntry.getTuples().size(); i < numTuples; ++i) {
                        for (Sort sort : headTypes) {
                            exprs.add(context.mkFreshConst("z", sort));
                        }
                    }
                }
                ++queryNumber;
            }
        }
        return exprs.toArray(new Expr[0]);
    }

    @Override
    public BoolExpr makeFormula(QueryTrace queries, Expr[] constants) {
        Query query = queries.getCurrentQuery().getQuery().getSolverQuery(schema, "cq_p", 0);
        return context.mkNot(query.apply(context, inst1).equalsExpr(context, query.apply(context, inst2)));
    }

    @Override
    protected String makeFormulaSMT(QueryTrace queries, Expr[] constants) {
        return super.makeFormulaSMT(queries, new Expr[0]) + "\n" + generateAssertions(queries, constants);
    }

    @Override
    public synchronized String generateSMT(QueryTrace queries) {
        return replaceStrings(replaceInts(super.generateSMT(queries)));
    }

    private static String replaceInts(String smt) {
        Set<String> ints = new HashSet<>();

        java.util.regex.Pattern pattern = Pattern.compile("\\(- (\\d+)\\)");
        Matcher matcher = pattern.matcher(smt);
        StringBuffer body1 = new StringBuffer();
        while (matcher.find()) {
            matcher.appendReplacement(body1, "");
            String s = matcher.group(1);
            ints.add("-" + s);
            body1.append(" int!-").append(s);
        }
        matcher.appendTail(body1);

        pattern = Pattern.compile("\\s(\\d+)");
        matcher = pattern.matcher(body1.toString());
        StringBuffer body2 = new StringBuffer();
        while (matcher.find()) {
            matcher.appendReplacement(body2, "");
            String s = matcher.group(1);
            ints.add(s);
            body2.append(" int!").append(s);
        }
        matcher.appendTail(body2);

        StringBuffer out = new StringBuffer("(declare-sort INT 0)\n");
        for (String i : ints) {
            out.append("(declare-fun int!").append(i).append(" () INT)\n");
        }
        out.append("(assert (distinct");
        for (String i : ints) {
            out.append(" int!").append(i);
        }
        out.append("))\n").append(body2);

        return out.toString().replaceAll("Int", "INT");
    }

    private static String replaceStrings(String smt) {
        Map<String, Integer> replacement = new HashMap<>();

        java.util.regex.Pattern pattern = Pattern.compile("\"([^\"]*)\"");
        Matcher matcher = pattern.matcher(smt);
        StringBuffer body = new StringBuffer();
        while (matcher.find()) {
            matcher.appendReplacement(body, "");
            String s = matcher.group(1);
            if (!replacement.containsKey(s)) {
                replacement.put(s, replacement.size());
            }
            body.append("string!").append(replacement.get(s));
        }
        matcher.appendTail(body);

        StringBuffer out = new StringBuffer("(declare-sort STRING 0)\n");
        for (int i = 0; i < replacement.size(); ++i) {
            out.append("(declare-fun string!").append(i).append(" () STRING)\n");
        }
        out.append("(assert (distinct");
        for (int i = 0; i < replacement.size(); ++i) {
            out.append(" string!").append(i);
        }
        out.append("))\n").append(body);

        return out.toString().replaceAll("String", "STRING");
    }
}
