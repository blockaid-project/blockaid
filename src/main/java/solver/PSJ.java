package solver;

import com.microsoft.z3.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;

public abstract class PSJ extends Query {
    Schema schema;
    List<String> relations;

    public PSJ(Schema schema, List<String> relations) {
        this.schema = schema;
        this.relations = relations;
    }

    protected BoolExpr predicateGenerator(Tuple... tuples) {
        return schema.getContext().mkBool(true);
    }

    protected abstract Tuple headSelector(Tuple... tuples);
    protected abstract Sort[] headTypeSelector(Sort[]... types);

    @Override
    public Sort[] headTypes() {
        List<Sort[]> args = new ArrayList<>();
        for (String relationName : relations) {
            args.add(schema.getColumns(relationName).stream().map(c -> c.type).toArray(Sort[]::new));
        }
        return headTypeSelector(args.toArray(new Sort[0][]));
    }

    @Override
    public BoolExpr doesContain(Instance instance, Tuple tuple) {
        // Returns a formula stating that tuple is in the output of this query on the instance.
        Tuple[] symbolicTups = relations.stream().map(r -> schema.makeFreshTuple(r)).toArray(Tuple[]::new);
        BoolExpr predicate = predicateGenerator(symbolicTups);
        Tuple headSymTup = headSelector(symbolicTups);
        checkArgument(headSymTup.size() == tuple.size());

        BoolExpr[] bodyExprs = new BoolExpr[relations.size()];
        for (int i = 0; i < relations.size(); ++i) {
            String relationName = relations.get(i);
            Tuple tup = symbolicTups[i];
            bodyExprs[i] = instance.get(relationName).apply(tup.toArray(new Expr[0]));
        }

        Context context = schema.getContext();
        BoolExpr bodyFormula = context.mkAnd(bodyExprs);
        Set<Expr> existentialVars = new HashSet<>();
        for (Tuple tup : symbolicTups) {
            existentialVars.addAll(tup);
        }
        for (Expr expr : headSymTup) {
            existentialVars.remove(expr);
        }

        for (int i = 0; i < tuple.size(); ++i) {
            bodyFormula = (BoolExpr) bodyFormula.substitute(headSymTup.get(i), tuple.get(i));
            predicate = (BoolExpr) predicate.substitute(headSymTup.get(i), tuple.get(i));
        }

        if (existentialVars.isEmpty()) {
            return context.mkAnd(bodyFormula, predicate);
        }

        return context.mkExists(existentialVars.toArray(new Expr[0]), context.mkAnd(bodyFormula, predicate), 1, null, null, null, null);
    }
}
