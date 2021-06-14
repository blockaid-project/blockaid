package solver;

import cache.QueryTrace;
import com.microsoft.z3.BoolExpr;

import java.util.*;
import java.util.stream.Collectors;

public class BoundedDeterminacyFormula extends DeterminacyFormula {
    // TODO this
    private static Map<String, Integer> makeBoundsMap(Schema schema) {
        Map<String, Integer> m = new HashMap<>();
        for (String relationName : schema.getRelationNames()) {
            m.put(relationName, 2);
        }
        return m;
    }

    public BoundedDeterminacyFormula(Schema schema, Collection<Query> views) {
        super(schema, (Integer instNum) -> schema.makeConcreteInstance("instance" + instNum, makeBoundsMap(schema)), (Instance inst1, Instance inst2) -> {
            List<BoolExpr> clauses = new ArrayList<>();
            if (inst1.constraint != null) {
                clauses.add(inst1.constraint);
            }
            if (inst2.constraint != null) {
                clauses.add(inst2.constraint);
            }
            for (Query v : views) {
                clauses.add(v.apply(inst1).equalsExpr(v.apply(inst2)));
            }
            return schema.getContext().mkAnd(clauses.toArray(new BoolExpr[0]));
        });
    }

    @Override
    public BoolExpr makeFormula(QueryTrace queries) {
        Query query = queries.getCurrentQuery().getQuery().getSolverQuery(schema);
        return context.mkAnd(
                context.mkNot(query.apply(inst1).equalsExpr(query.apply(inst2))),
                generateTupleCheck(queries)
        );
    }

    @Override
    protected String makeFormulaSMT(QueryTrace queries) {
        return "(set-option :smt.macro-finder true)\n" +
                "(assert " + makeFormula(queries).toString() + ")";
    }
}
