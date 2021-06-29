package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.*;
import policy_checker.Policy;

import java.util.*;

public class UnsatCoreDeterminacyFormula extends DeterminacyFormula {
    private final boolean unnamedEquality;
    private final boolean eliminateIrrelevant;
    private final ImmutableSet<String> relevantAttributes;

    public UnsatCoreDeterminacyFormula(Schema schema, Collection<Policy> policies, Collection<Query> views, boolean unnamedEquality, boolean eliminateIrrelevant) {
        super(schema,
                (Integer instNum) -> schema.makeFreshInstance("instance" + instNum),
                (Instance inst1, Instance inst2) -> {
                    List<BoolExpr> clauses = new ArrayList<>();
                    clauses.addAll(inst1.constraints);
                    clauses.addAll(inst2.constraints);
                    for (Query v : views) {
                        clauses.add(v.apply(inst1).equalsExpr(v.apply(inst2)));
                    }
                    return clauses;
                });

        this.unnamedEquality = unnamedEquality;
        this.eliminateIrrelevant = eliminateIrrelevant;
        this.relevantAttributes = policies.stream()
                .flatMap(policy -> policy.getThetaColumns().stream())
                .collect(ImmutableSet.toImmutableSet());
    }

    private Map<Object, Integer> assertionMap = null;
    public Map<Object, Integer> getAssertionMap() {
        return assertionMap;
    }

    private String generateAssertions(QueryTrace queries) {
        Map<String, BoolExpr> exprs = new HashMap<>();

        int queryNumber = 0;
        Map<Object, Set<Expr>> equalitySets = new HashMap<>();
        for (QueryTraceEntry queryTraceEntry : queries.getAllEntries()) {
            String prefix = (queryTraceEntry == queries.getCurrentQuery() ? "cq_p" : ("q_p!" + queryNumber));
            Query query = queryTraceEntry.getQuery().getSolverQuery(schema, prefix, 0);

            List<String> paramNames = queryTraceEntry.getQuery().paramNames;
            List<Object> parameters = queryTraceEntry.getQuery().parameters;
            Expr[] paramExprs = new Expr[parameters.size()];
            for (int i = 0; i < parameters.size(); ++i) {
                paramExprs[i] = context.mkConst("!" + prefix + "!" + i, Tuple.getSortFromObject(context, parameters.get(i)));
            }
            Tuple paramConstants = new Tuple(schema, paramExprs);

            Relation r1 = query.apply(inst1);
            Relation r2 = query.apply(inst2);
            if (queryTraceEntry.hasTuples() || queryTraceEntry == queries.getCurrentQuery()) {
                for (int i = 0; i < parameters.size(); ++i) {
                    if (paramNames.get(i).equals("?")) {
                        Object p = parameters.get(i);
                        if (!equalitySets.containsKey(p)) {
                            // these should be linked to the query assertions since that's the only place where the
                            // constants are even used, except for the current query but that's special cased elsewhere
                            exprs.put("a_pv!" + queryNumber + "!" + i, context.mkEq(paramConstants.get(i), Tuple.getExprFromObject(context, p)));
                            equalitySets.put(p, new HashSet<>());
                        }
                        equalitySets.get(p).add(paramConstants.get(i));
                    }
                }
            }

            if (queryTraceEntry.hasTuples()) {
                int numAttrs = query.headTypes().length;

                List<Tuple> tupleConstants = new ArrayList<>();
                List<String> attributeNames = queryTraceEntry.getQuery().getProjectColumns();
                int attrNumber = 0;
                for (List<Object> tuple : queryTraceEntry.getTuples()) {
                    Expr[] tupleExprs = new Expr[numAttrs];
                    Sort[] headTypes = query.headTypes();
                    for (int i = 0; i < numAttrs; ++i) {
                        tupleExprs[i] = context.mkFreshConst("z", headTypes[i]);
                    }
                    Tuple tupleConstant = new Tuple(schema, tupleExprs);
                    tupleConstants.add(tupleConstant);
                    for (int i = 0; i < tuple.size(); ++i) {
                        Object curr = tuple.get(i);
                        if (curr == null) {
                            continue;
                        }
                        if (!eliminateIrrelevant || relevantAttributes.contains(attributeNames.get(i))) {
                            if (!equalitySets.containsKey(curr)) {
                                exprs.put("a_v!" + queryNumber + "!" + attrNumber, context.mkEq(tupleConstant.get(i), Tuple.getExprFromObject(context, curr)));
                                equalitySets.put(curr, new HashSet<>());
                            }
                            equalitySets.get(curr).add(tupleConstant.get(i));
                        }

                        ++attrNumber;
                    }
                }

                exprs.put("a_q!" + queryNumber, context.mkAnd(r1.doesContain(tupleConstants), r2.doesContain(tupleConstants)));
            }

            ++queryNumber;
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
    public Iterable<BoolExpr> makeFormula(QueryTrace queries) {
        throw new UnsupportedOperationException();
    }

    private String makeMainSMT(QueryTrace queries) {
        Query query = queries.getCurrentQuery().getQuery().getSolverQuery(schema, "cq_p", 0);
        return "(assert " + context.mkNot(query.apply(inst1).equalsExpr(query.apply(inst2))) + ")";
    }

    @Override
    protected String makeFormulaSMT(QueryTrace queries) {
        return makeMainSMT(queries) + "\n" + generateAssertions(queries);
    }
}
