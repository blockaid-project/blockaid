package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.microsoft.z3.*;

import java.util.*;

public class UnsatCoreDeterminacyFormula extends DeterminacyFormula {
    private final boolean unnamedEquality;

    public UnsatCoreDeterminacyFormula(Context context, Schema schema, Collection<Query> views, boolean unnamedEquality) {
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
                List<Object> parameters = queryTraceEntry.getQuery().parameters;
                Tuple paramConstants = new Tuple(Arrays.copyOfRange(constants, constantsOffset, constantsOffset + parameters.size()));
                constantsOffset += parameters.size();
                for (int i = 0; i < parameters.size(); ++i) {
                    if (paramNames.get(i).equals("?")) {
                        Object currParam = parameters.get(i);

                        // these should be linked to the query assertions since that's the only place where the
                        // constants are even used, except for the current query but that's special cased elsewhere
                        exprs.put("a_pv!" + queryNumber + "!" + i, context.mkEq(paramConstants.get(i), Tuple.getExprFromObject(context, currParam)));

                        equalitySets.putIfAbsent(currParam, new HashSet<>());
                        equalitySets.get(currParam).add(paramConstants.get(i));
                    }
                }

                Relation r1 = query.apply(context, inst1);
                Relation r2 = query.apply(context, inst2);
                if (!queryTraceEntry.getTuples().isEmpty()) {
                    int numAttrs = query.headTypes().length;

                    List<Tuple> tupleConstants = new ArrayList<>();
                    int attrNumber = 0;
                    for (List<Object> tuple : queryTraceEntry.getTuples()) {
                        Tuple tupleConstant = new Tuple(Arrays.copyOfRange(constants, constantsOffset, constantsOffset + numAttrs));
                        tupleConstants.add(tupleConstant);
                        for (int i = 0; i < tuple.size(); ++i) {
                            exprs.put("a_v!" + queryNumber + "!" + attrNumber, context.mkEq(tupleConstant.get(i), Tuple.getExprFromObject(context, tuple.get(i))));

                            equalitySets.putIfAbsent(tuple.get(i), new HashSet<>());
                            equalitySets.get(tuple.get(i)).add(tupleConstant.get(i));

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
                List<Object> parameters = queryTraceEntry.getQuery().parameters;
                for (int i = 0; i < parameters.size(); ++i) {
                    exprs.add(context.mkConst("!" + prefix + "!" + i, Tuple.getSortFromObject(context, parameters.get(i))));
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
}
