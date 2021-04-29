package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.microsoft.z3.*;

import java.util.*;
import java.util.stream.Collectors;

public class UnsatCoreDeterminacyFormula extends DeterminacyFormula {
    public UnsatCoreDeterminacyFormula(Context context, Schema schema, Collection<Query> views) {
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
    }

    private Map<QueryTraceEntry, String> assertionMap = null;

    public Map<QueryTraceEntry, String> getAssertionMap() {
        return assertionMap;
    }

    private String generateAssertions(QueryTrace queries, Expr[] constants) {
        Map<String, BoolExpr> exprs = new HashMap<>();
        this.assertionMap = new HashMap<>();

        int constantsOffset = 0;
        int queryNumber = 0;
        for (List<QueryTraceEntry> queryTraceEntries : queries.getQueries().values()) {
            for (QueryTraceEntry queryTraceEntry : queryTraceEntries) {
                String prefix = (queryTraceEntry == queries.getCurrentQuery() ? "cq_p" : ("q_p!" + queryNumber));
                Query query = queryTraceEntry.getQuery().getSolverQuery(schema, prefix, 0);
                List<String> paramNames = queryTraceEntry.getQuery().paramNames;
                Object[] parameters = queryTraceEntry.getQuery().parameters;
                Tuple paramConstants = new Tuple(Arrays.copyOfRange(constants, constantsOffset, constantsOffset + parameters.length));
                constantsOffset += parameters.length;
                for (int i = 0; i < parameters.length; ++i) {
                    if (paramNames.get(i).equals("?")) {
                        // these should be linked to the query assertions since that's the only place where the
                        // constants are even used, except for the current query but that's special cased elsewhere
                        exprs.put("a_pv!" + queryNumber + "!" + i, context.mkEq(paramConstants.get(i), Tuple.getExprFromObject(context, parameters[i])));
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
                            ++attrNumber;
                        }
                        constantsOffset += numAttrs;
                    }

                    exprs.put("a_q!" + queryNumber, context.mkAnd(r1.doesContain(context, tupleConstants), r2.doesContain(context, tupleConstants)));
                }

                ++queryNumber;
            }
        }
        if (exprs.isEmpty()) {
            return "";
        }

        StringBuilder out = new StringBuilder();
        for (Map.Entry<String, BoolExpr> expr : exprs.entrySet()) {
            out.append("(assert (! ").append(expr.getValue().toString()).append(" :named ").append(expr.getKey()).append("))\n");
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
}
