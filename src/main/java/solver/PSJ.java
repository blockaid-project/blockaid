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

        HashMultimap<Expr, Expr> subs = HashMultimap.create(); // Substitute from -> to.
        for (int i = 0; i < tuple.size(); ++i) {
            subs.put(headSymTup.get(i), tuple.get(i));
        }

        // Substitute.
        ArrayList<Expr> substituteFrom = new ArrayList<>(), substituteTo = new ArrayList<>();
        for (Expr fromTerm : subs.keySet()) {
            Set<Expr> targets = subs.get(fromTerm);
            substituteFrom.add(fromTerm);

            Expr canonicalToTerm = null;
            for (Expr toTerm : targets) {
                if (canonicalToTerm == null) {
                    canonicalToTerm = toTerm;
                    substituteTo.add(toTerm);
                } else {
                    // Two exprs in tuple map to the same symbolic head sym, so we have to constrain them to be equal.
                    bodyClauses.add(context.mkEq(toTerm, canonicalToTerm));
                }
            }
        }

        Set<Expr> existentialVars = Arrays.stream(symbolicTups).flatMap(Tuple::stream).collect(Collectors.toSet());
        headSymTup.stream().forEach(existentialVars::remove);
        BoolExpr body = (BoolExpr) context.mkAnd(bodyClauses)
                .substitute(substituteFrom.toArray(new Expr[0]), substituteTo.toArray(new Expr[0]));
        return List.of(context.myMkExists(existentialVars, body));
    }

    // FIXME(zhangwen): these optimizations seem to break something. (e.g., if the same column is projected twice)
//    @Override
//    public Iterable<BoolExpr> doesContain(Instance instance, Tuple tuple) {
//        Tuple[] symbolicTups = new Tuple[relations.size()];
//        for (int i = 0; i < relations.size(); ++i) {
//            String relationName = relations.get(i);
//            // We'll look for the identifier string `mdct!` later on.
//            symbolicTups[i] = schema.makeNamedTuple(relationName, "mdct!" + i);
//        }
//
////        Tuple[] symbolicTups = relations.stream().map(r -> schema.makeFreshTuple(r, "mdct")).toArray(Tuple[]::new);
//        BoolExpr predicate = predicateGenerator(symbolicTups);
//        Tuple headSymTup = headSelector(symbolicTups);
//
//        MyZ3Context context = schema.getContext();
//        ImmutableSet<Expr> allVars = Arrays.stream(symbolicTups).flatMap(Tuple::stream)
//                .collect(ImmutableSet.toImmutableSet());
//        Set<Expr> existentialVars = new HashSet<>(allVars);
//        headSymTup.stream().forEach(existentialVars::remove);
//
//        Substitutions<Expr> subs = new Substitutions<>(allVars);
//        //region Compute substitution for each tuple variable that is always equal to another expr
//        List<Equality> eqs = extractEqFromConj(predicate).collect(Collectors.toList());
//        {
//            Set<Expr> exprs = eqs.stream().flatMap(eq -> Stream.of(eq.lhs, eq.rhs)).collect(Collectors.toSet());
//            exprs.addAll(allVars);
//            exprs.addAll(Arrays.asList(tuple.toExprArray()));
//            UnionFind<Expr> uf = new UnionFind<>(exprs);
//
//            for (int i = 0; i < tuple.size(); ++i) {
////                System.out.println("UNION\t" + headSymTup.get(i) + "\t" + tuple.get(i));
//                uf.union(headSymTup.get(i), tuple.get(i));
//            }
//            for (Equality eq : eqs) {
////                System.out.println("UNION\t" + eq.lhs + "\t" + eq.rhs);
//                uf.union(eq.lhs, eq.rhs);
//            }
//            for (Expr e : exprs) {
//                UnionFind<Expr>.EquivalenceClass ec = uf.findComplete(e);
//                if (ec.getDatum() == null && !allVars.contains(e)) {
////                    System.out.println("DATA " + e);
//                    uf.attachData(e, e);
//                }
//            }
//
//            Set<Expr> replaced = new HashSet<>();
//            for (Expr e : allVars) {
//                UnionFind<Expr>.EquivalenceClass ec = uf.findComplete(e);
//                Expr replaceWith = (Expr) ec.getDatum();
//                if (replaceWith == null) {
//                    replaceWith = ec.getRoot();
//                    checkState(existentialVars.contains(replaceWith));
//                }
//                if (!replaceWith.equals(e)) {
//                    subs.set(e, replaceWith);
//                    replaced.add(e);
//                }
//            }
//            existentialVars.removeAll(replaced);
//        }
//        //endregion
//
//        //region Substitute variables in the predicate
//        {
//            List<Expr> subFrom = new ArrayList<>(), subTo = new ArrayList<>();
//            for (Map.Entry<Expr, Expr> entry: subs.entrySet()) {
//                if (!entry.getValue().equals(entry.getKey())) {
//                    subFrom.add(entry.getKey());
//                    subTo.add(entry.getValue());
//                }
//            }
//            predicate = (BoolExpr) predicate.substitute(subFrom.toArray(new Expr[0]), subTo.toArray(new Expr[0]))
//                    .simplify(); // Get rid of equalities like `x = x`.
//        }
//        //endregion
//
//        //region Substitute variables in the symbolic tuples and head sym
//        for (int i = 0; i < symbolicTups.length; ++i) {
//            Tuple newTup = new Tuple(schema, symbolicTups[i].stream().map(subs::get));
//            symbolicTups[i] = newTup;
//        }
////        headSymTup = new Tuple(schema, headSymTup.stream().map(subs::get));
//        //endregion
//
//        BoolExpr[] bodyClauses = new BoolExpr[relations.size()];
//        for (int i = 0; i < relations.size(); ++i) {
//            String relationName = relations.get(i);
//            Tuple tup = symbolicTups[i];
//            bodyClauses[i] = context.mkAnd(instance.get(relationName).doesContainExpr(tup));
//        }
//
////        BoolExpr naive =
////                context.myMkExists(existentialVars,
////                        context.mkAnd(context.mkAnd(bodyClauses), predicate));
//
//        List<BoolExpr> body = new ArrayList<>();
//
//        if (predicate.getSExpr().contains("mdct!")) {
//            // TODO(zhangwen): implement the case where predicate uses existential?
////            System.out.println("Naive:");
////            System.out.println(naive);
////            System.out.println("eqs = " + eqs);
////            System.out.println("subs = " + subs);
////            System.out.println("***");
//            body.add(context.myMkExists(existentialVars,
//                    context.mkAnd(context.mkAnd(bodyClauses), predicate)));
//        } else {
//            List<Set<Expr>> usedEvs = new ArrayList<>();
//            for (int i = 0; i < symbolicTups.length; ++i) {
//                Set<Expr> vs = symbolicTups[i].stream().collect(Collectors.toSet());
//                vs.retainAll(existentialVars);
//                usedEvs.add(i, vs);
//            }
//
//            UnionFind<Integer> uf = new UnionFind<>(IntStream.range(0, symbolicTups.length).boxed());
//            for (int i = 0; i < symbolicTups.length; ++i) {
//                for (int j = i + 1; j < symbolicTups.length; ++j) {
//                    if (!Sets.intersection(usedEvs.get(i), usedEvs.get(j)).isEmpty()) {
//                        uf.union(i, j);
//                    }
//                }
//            }
//
//            for (Integer thisRoot : uf.getRoots()) {
//                List<BoolExpr> thisPart = new ArrayList<>();
//                Set<Expr> thisPartEvs = new HashSet<>();
//                for (int i = 0; i < symbolicTups.length; ++i) {
//                    if (uf.find(i).equals(thisRoot)) {
//                        thisPart.add(bodyClauses[i]);
//                        thisPartEvs.addAll(usedEvs.get(i));
//                    }
//                }
//
//                BoolExpr thisPartConjunction = context.mkAnd(thisPart.toArray(new BoolExpr[0]));
//                if (thisPartEvs.isEmpty()) {
//                    body.add(thisPartConjunction);
//                } else {
//                    body.add(context.mkExists(thisPartEvs.toArray(new Expr[0]), thisPartConjunction, 1, null,
//                            null, null, null));
//                }
//            }
//
//            if (!predicate.isTrue()) {
//                body.add(predicate);
//            }
//
////            if (body.size() >= 2) {
////                System.out.println("Naive:");
////                System.out.println(naive);
////                System.out.println("Split:");
////                for (BoolExpr b : body) {
////                    System.out.println(b);
////                }
////                System.out.println("***");
////            }
//        }
//
//        return body;
////        Expr[] headSymTupArr = headSymTup.toExprArray();
////        return context.mkAnd(body.stream().map(e -> (BoolExpr) e.substitute(headSymTupArr, tuple.toExprArray()))
////                .toArray(BoolExpr[]::new));
//    }

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
        visitJoins(instance, (Tuple[] ts, BoolExpr[] es) -> {
            exprs.add(context.mkAnd(context.mkAnd(es), predicateGenerator(ts)));
        });
        return exprs.toArray(new BoolExpr[0]);
    }
}
