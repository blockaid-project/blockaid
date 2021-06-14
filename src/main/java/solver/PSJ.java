package solver;

import com.microsoft.z3.*;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
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
            bodyExprs[i] = instance.get(relationName).apply(tup);
        }

        Context context = schema.getContext();
        BoolExpr bodyFormula = context.mkAnd(bodyExprs);
        Set<Expr> existentialVars = Arrays.stream(symbolicTups).flatMap(Tuple::stream).collect(Collectors.toSet());
        for (Expr expr : headSymTup.content()) {
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

    private void visitJoins(Instance instance, BiConsumer<Tuple[], BoolExpr[]> consumer, List<Tuple> tuples, List<BoolExpr> exists, int index) {
        if (index == relations.size()) {
            consumer.accept(tuples.toArray(new Tuple[0]), exists.toArray(new BoolExpr[0]));
            return;
        }
        String relationName = relations.get(index);
        ConcreteRelation relation = (ConcreteRelation) instance.get(relationName);
        Tuple[] t = relation.getTuples();
        BoolExpr[] e = relation.getExists();
        for (int i = 0; i < t.length; ++i) {
            tuples.add(t[i]);
            exists.add(e[i]);
            visitJoins(instance, consumer, tuples, exists, index + 1);
            exists.remove(exists.size() - 1);
            tuples.remove(tuples.size() - 1);
        }
    }

    @Override
    public Tuple[] generateTuples(Instance instance) {
        checkArgument(instance.isConcrete);

        final List<Tuple> tuples = new ArrayList<>();
        visitJoins(instance, (Tuple[] ts, BoolExpr[] es) -> {
            tuples.add(headSelector(ts));
        }, new ArrayList<>(), new ArrayList<>(), 0);
        return tuples.toArray(new Tuple[0]);
    }

    @Override
    public BoolExpr[] generateExists(Instance instance) {
        checkArgument(instance.isConcrete);

        final Context context = instance.getContext();
        final List<BoolExpr> exprs = new ArrayList<>();
        visitJoins(instance, (Tuple[] ts, BoolExpr[] es) -> {
            exprs.add(context.mkAnd(context.mkAnd(es), predicateGenerator(ts)));
        }, new ArrayList<>(), new ArrayList<>(), 0);
        return exprs.toArray(new BoolExpr[0]);
    }
}
