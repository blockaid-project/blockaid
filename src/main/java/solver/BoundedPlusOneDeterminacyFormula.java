package solver;

import cache.QueryTrace;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

import java.util.*;
import java.util.function.Function;

public class BoundedPlusOneDeterminacyFormula extends DeterminacyFormula {
    private String assertions;

    private static Function<Integer, Instance> getInstanceMaker(Schema schema, Map<String, Integer> bounds) {
        Map<String, Integer> incrementedBounds = new HashMap<>(bounds);
        for (String s : bounds.keySet()) {
            incrementedBounds.computeIfPresent(s, (k, v) -> v + 1);
        }
        return (Integer instNum) -> schema.makeConcreteInstance("instance" + instNum, incrementedBounds);
    }

    public BoundedPlusOneDeterminacyFormula(Schema schema, Collection<Query> views, Map<String, Integer> bounds) {
        super(schema, getInstanceMaker(schema, bounds), (Instance inst1, Instance inst2) -> {
            List<BoolExpr> clauses = new ArrayList<>();
            clauses.addAll(inst1.getConstraints().values());
            clauses.addAll(inst2.getConstraints().values());
            for (Query v : views) {
                clauses.add(v.apply(inst1).equalsExpr(v.apply(inst2)));
            }
            return clauses;
        });
    }

    @Override
    protected BoolExpr additionalAssertion(Context context) {
        Map<String, BoolExpr> exprs = new HashMap<>();

        for (String relation : schema.getRelationNames()) {
            String suffix = "_" + relation + "_" + 0 + "_exists";
            BoolExpr expr = context.mkAnd(
                    context.mkEq(context.mkConst("instance0" + suffix, context.getBoolSort()), context.mkFalse()),
                    context.mkEq(context.mkConst("instance1" + suffix, context.getBoolSort()), context.mkFalse())
            );
            exprs.put(relation, expr);
        }

        // to avoid missing variable declarations because some relations may be entirely dropped if bounds are 0
        StringBuilder out = new StringBuilder();
        List<BoolExpr> exprParts = new ArrayList<>();
        for (Map.Entry<String, BoolExpr> expr : exprs.entrySet()) {
            BoolExpr tag = (BoolExpr) context.mkConst("assertion_tag!" + expr.getKey(), context.getBoolSort());
            exprParts.add(context.mkEq(tag, expr.getValue()));
            out.append("(assert (! ").append("assertion_tag!" + expr.getKey()).append(" :named ").append(expr.getKey()).append("))\n");
        }
        this.assertions = out.toString();
        return context.mkAnd(exprParts.toArray(new BoolExpr[0]));
    }

    @Override
    protected String makeFormulaSMT(QueryTrace queries) {
        return super.makeFormulaSMT(queries) + "\n" + assertions;
    }
}
