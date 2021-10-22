package solver;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Multimap;
import com.microsoft.z3.*;
import solver.context.MyZ3Context;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public abstract class PSJ extends Query {
    private final Schema schema;
    private final List<String> relations;
    private final Map<Instance, Function<Tuple, BoolExpr>> inst2DoesContainTemplate = new HashMap<>();

    @Override
    public Schema getSchema() {
        return schema;
    }

    public PSJ(Schema schema, List<String> relations) {
        this.schema = schema;
        this.relations = relations;
    }

    protected BoolExpr predicateGenerator(Tuple... tuples) {
        return schema.getContext().mkTrue();
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

    private static class Equality {
        private final Expr lhs;
        private final Expr rhs;

        public Equality(Expr lhs, Expr rhs) {
            this.lhs = lhs;
            this.rhs = rhs;
        }

        @Override
        public String toString() {
            return "Equality{" +
                    "lhs=" + lhs +
                    ", rhs=" + rhs +
                    '}';
        }
    }

    private static Stream<Equality> extractEqFromConj(Expr predicate) {
        if (predicate.isEq()) {
            Expr[] eqArgs = predicate.getArgs();
            return Stream.of(new Equality(eqArgs[0], eqArgs[1]));
        }
        if (!predicate.isAnd()) {
            return Stream.empty();
        }
        return Arrays.stream(predicate.getArgs()).flatMap(PSJ::extractEqFromConj);
    }

    // Returns a formula stating that tuple is in the output of this query on the instance.
    @Override
    public Iterable<BoolExpr> doesContain(Instance instance, Tuple tuple) {
        List<BoolExpr> bodyClauses = new ArrayList<>();
        Tuple[] symbolicTups = relations.stream().map(schema::makeFreshQuantifiedTuple).toArray(Tuple[]::new);
        Tuple headSymTup = headSelector(symbolicTups);
        checkArgument(headSymTup.size() == tuple.size());

        MyZ3Context context = schema.getContext();
        for (int i = 0; i < relations.size(); ++i) {
            String relationName = relations.get(i);
            Tuple tup = symbolicTups[i];
            Iterables.addAll(bodyClauses, instance.get(relationName).doesContainExpr(tup));
        }

        bodyClauses.add(predicateGenerator(symbolicTups)); // The WHERE clause.

        for (int i = 0; i < tuple.size(); ++i) {
            bodyClauses.add(context.mkEq(tuple.get(i), headSymTup.get(i)));
        }

        Set<Expr> existentialVars = Arrays.stream(symbolicTups).flatMap(Tuple::stream).collect(Collectors.toSet());
        BoolExpr body = context.mkAnd(bodyClauses);
        return List.of(
                context.eliminateQuantifiers(context.myMkExists(existentialVars, body))
        );
    }

    private void visitJoins(Instance instance, BiConsumer<Tuple[], BoolExpr[]> consumer) {
        visitJoins(instance, consumer, new ArrayList<>(), new ArrayList<>(), 0);
    }

    private void visitJoins(Instance instance, BiConsumer<Tuple[], BoolExpr[]> consumer, List<Tuple> tuples, List<BoolExpr> exists, int index) {
        checkArgument(0 <= index && index <= relations.size());
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
        visitJoins(instance, (Tuple[] ts, BoolExpr[] es) -> tuples.add(headSelector(ts)));
        return tuples.toArray(new Tuple[0]);
    }

    @Override
    public BoolExpr[] generateExists(Instance instance) {
        checkArgument(instance.isConcrete);

        final MyZ3Context context = instance.getContext();
        final List<BoolExpr> exprs = new ArrayList<>();
        visitJoins(instance, (Tuple[] ts, BoolExpr[] es) ->
                exprs.add(context.mkAnd(context.mkAnd(es), predicateGenerator(ts)))
        );
        return exprs.toArray(new BoolExpr[0]);
    }
}
