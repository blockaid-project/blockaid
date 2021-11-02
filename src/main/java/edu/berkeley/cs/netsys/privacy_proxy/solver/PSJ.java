package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.Iterables;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;

public abstract class PSJ<C extends Z3ContextWrapper<?, ?, ?, ?>> extends Query<C> {
    private final Schema<C> schema;
    private final List<String> relations;
    private final Map<Instance<C>, Function<Tuple<C>, BoolExpr>> inst2DoesContainTemplate = new HashMap<>();

    @Override
    public Schema<C> getSchema() {
        return schema;
    }

    public PSJ(Schema<C> schema, List<String> relations) {
        this.schema = schema;
        this.relations = relations;
    }

    protected BoolExpr predicateGenerator(List<Tuple<C>> tuples) {
        return schema.getContext().mkTrue();
    }

    protected abstract Tuple<C> headSelector(List<Tuple<C>> tuples);
    protected abstract Sort[] headTypeSelector(Sort[]... types);

    @Override
    public Sort[] headTypes() {
        List<Sort[]> args = new ArrayList<>();
        for (String relationName : relations) {
            args.add(schema.getColumns(relationName).stream().map(Column::type).toArray(Sort[]::new));
        }
        return headTypeSelector(args.toArray(new Sort[0][]));
    }

    // Returns a formula stating that tuple is in the output of this query on the instance.
    @Override
    public Iterable<BoolExpr> doesContain(Instance<C> instance, Tuple<C> tuple) {
        List<BoolExpr> bodyClauses = new ArrayList<>();
        List<Tuple<C>> symbolicTuples = relations.stream().map(schema::makeFreshQuantifiedTuple).collect(Collectors.toList());
        Tuple<C> headSymTup = headSelector(symbolicTuples);
        checkArgument(headSymTup.size() == tuple.size());

        C context = schema.getContext();
        for (int i = 0; i < relations.size(); ++i) {
            String relationName = relations.get(i);
            Tuple<C> tup = symbolicTuples.get(i);
            Iterables.addAll(bodyClauses, instance.get(relationName).doesContainExpr(tup));
        }

        bodyClauses.add(predicateGenerator(symbolicTuples)); // The WHERE clause.

        for (int i = 0; i < tuple.size(); ++i) {
            bodyClauses.add(context.mkEq(tuple.get(i), headSymTup.get(i)));
        }

        Set<Expr<?>> existentialVars = symbolicTuples.stream().flatMap(Tuple::stream).collect(Collectors.toSet());
        BoolExpr body = context.mkAnd(bodyClauses);
        return List.of(
                context.eliminateQuantifiers(context.myMkExists(existentialVars, body))
        );
    }

    private void visitJoins(Instance<C> instance, BiConsumer<List<Tuple<C>>, List<BoolExpr>> consumer) {
        visitJoins(instance, consumer, new ArrayList<>(), new ArrayList<>(), 0);
    }

    private void visitJoins(Instance<C> instance, BiConsumer<List<Tuple<C>>, List<BoolExpr>> consumer, List<Tuple<C>> tuples, List<BoolExpr> exists, int index) {
        checkArgument(0 <= index && index <= relations.size());
        if (index == relations.size()) {
            consumer.accept(tuples, exists);
            return;
        }
        String relationName = relations.get(index);
        ConcreteRelation<C> relation = (ConcreteRelation<C>) instance.get(relationName);
        List<Tuple<C>> t = relation.getTuples();
        List<BoolExpr> e = relation.getExists();
        for (int i = 0; i < t.size(); ++i) {
            tuples.add(t.get(i));
            exists.add(e.get(i));
            visitJoins(instance, consumer, tuples, exists, index + 1);
            exists.remove(exists.size() - 1);
            tuples.remove(tuples.size() - 1);
        }
    }

    @Override
    public List<Tuple<C>> generateTuples(Instance<C> instance) {
        checkArgument(instance.isConcrete);

        List<Tuple<C>> tuples = new ArrayList<>();
        visitJoins(instance, (List<Tuple<C>> ts, List<BoolExpr> es) -> tuples.add(headSelector(ts)));
        return tuples;
    }

    @Override
    public List<BoolExpr> generateExists(Instance<C> instance) {
        checkArgument(instance.isConcrete);

        C context = instance.getContext();
        List<BoolExpr> exprs = new ArrayList<>();
        visitJoins(instance, (List<Tuple<C>> ts, List<BoolExpr> es) ->
                exprs.add(context.mkAnd(context.mkAnd(es), predicateGenerator(ts)))
        );
        return exprs;
    }
}
