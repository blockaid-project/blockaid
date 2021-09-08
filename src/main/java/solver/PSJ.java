package solver;

import antlr.collections.impl.IntRange;
import cache.labels.ReturnedRowLabel;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Sets;
import com.microsoft.z3.*;
import org.apache.calcite.rel.core.Union;
import util.UnionFind;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
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

    private void splitExistential(Expr[] existentialVars, Expr body) {
        List<Expr> newBodies;
        if (!body.isAnd()) {
            newBodies = List.of(body);
        } else {

        }
    }

    public Function<Tuple, BoolExpr> makeDoesContainTemplate(Instance instance) {
        Tuple[] symbolicTups = relations.stream().map(r -> schema.makeFreshTuple(r, "mdct")).toArray(Tuple[]::new);
        BoolExpr predicate = predicateGenerator(symbolicTups);
        Tuple headSymTup = headSelector(symbolicTups);

        MyZ3Context context = schema.getContext();
        Set<Expr> allVars = Arrays.stream(symbolicTups).flatMap(Tuple::stream).collect(Collectors.toSet());
        Set<Expr> existentialVars = new HashSet<>(allVars);
        headSymTup.stream().forEach(existentialVars::remove);

        Map<Expr, Expr> substitutions = new HashMap<>();
        for (Expr e : allVars) {
            substitutions.put(e, e);
        }

        //region Compute substitution for each existential variable that is always equal to another expr
        {
            List<Equality> eqs = extractEqFromConj(predicate).collect(Collectors.toList());
            Set<Expr> exprs = eqs.stream().flatMap(eq -> Stream.of(eq.lhs, eq.rhs)).collect(Collectors.toSet());
            UnionFind<Expr> uf = new UnionFind<>(exprs);
            for (Equality eq : eqs) {
                uf.union(eq.lhs, eq.rhs);
            }
            for (Expr e : exprs) {
                if (!allVars.contains(e)) { // This is a constant (?)
                    uf.attachData(e, e);
                }
            }
            for (Expr e : exprs) {
                if (!existentialVars.contains(e)) {
                    UnionFind<Expr>.EquivalenceClass ec = uf.findComplete(e);
                    if (ec.getDatum() == null) { // This is in the head.
                        uf.attachData(e, e);
                    }
                }
            }

            Set<Expr> replaced = new HashSet<>();
            for (Expr e : existentialVars) {
                if (!exprs.contains(e)) {
                    continue;
                }
                UnionFind<Expr>.EquivalenceClass ec = uf.findComplete(e);
                Expr replaceWith = (Expr) ec.getDatum();
                if (replaceWith == null) {
                    checkState(existentialVars.contains(e));
                    replaceWith = ec.getRoot();
                }
                if (!replaceWith.equals(e)) {
                    for (Map.Entry<Expr, Expr> entry: substitutions.entrySet()) {
                        if (entry.getValue().equals(e)) {
                            entry.setValue(replaceWith);
                        }
                    }
                    replaced.add(e);
                }
            }
            existentialVars.removeAll(replaced);
        }
        //endregion

        //region Substitute variables in the predicate
        {
            List<Expr> subFrom = new ArrayList<>(), subTo = new ArrayList<>();
            for (Map.Entry<Expr, Expr> entry: substitutions.entrySet()) {
                if (!entry.getValue().equals(entry.getKey())) {
                    subFrom.add(entry.getKey());
                    subTo.add(entry.getValue());
                }
            }
            predicate = (BoolExpr) predicate.substitute(subFrom.toArray(new Expr[0]), subTo.toArray(new Expr[0]))
                    .simplify(); // Get rid of equalities like `x = x`.
        }
        //endregion

        //region Substitute variables in the symbolic tuples and head sym
        for (int i = 0; i < symbolicTups.length; ++i) {
            Tuple newTup = new Tuple(schema, symbolicTups[i].stream().map(e -> substitutions.getOrDefault(e, e)));
            symbolicTups[i] = newTup;
        }
        headSymTup = new Tuple(schema, headSymTup.stream().map(e -> substitutions.getOrDefault(e, e)));
        //endregion

        BoolExpr[] bodyClauses = new BoolExpr[relations.size()];
        for (int i = 0; i < relations.size(); ++i) {
            String relationName = relations.get(i);
            Tuple tup = symbolicTups[i];
            bodyClauses[i] = instance.get(relationName).doesContainExpr(tup);
        }

        BoolExpr naive =
                context.myMkExists(existentialVars,
                        context.mkAnd(context.mkAnd(bodyClauses), predicate));

        List<BoolExpr> body = new ArrayList<>();

        Set<String> existentialVarNames = existentialVars.stream().map(Expr::getSExpr).collect(Collectors.toSet());
        boolean predUsesEv = Pattern.compile("mdct!\\d+").matcher(predicate.getSExpr()).results().anyMatch(mr -> existentialVarNames.contains(mr.group()));
//        boolean predUsesEv = true;
        if (predUsesEv) {
            // TODO(zhangwen): implement the case where predicate uses existential?
            body.add(context.myMkExists(existentialVars,
                    context.mkAnd(context.mkAnd(bodyClauses), predicate)));
        } else {
            List<Set<Expr>> usedEvs = new ArrayList<>();
            for (int i = 0; i < symbolicTups.length; ++i) {
                Set<Expr> vs = symbolicTups[i].stream().collect(Collectors.toSet());
                vs.retainAll(existentialVars);
                usedEvs.add(i, vs);
            }

            UnionFind<Integer> uf = new UnionFind<>(IntStream.range(0, symbolicTups.length).boxed());
            for (int i = 0; i < symbolicTups.length; ++i) {
                for (int j = i + 1; j < symbolicTups.length; ++j) {
                    if (!Sets.intersection(usedEvs.get(i), usedEvs.get(j)).isEmpty()) {
                        uf.union(i, j);
                    }
                }
            }

            for (Integer thisRoot : uf.getRoots()) {
                List<BoolExpr> thisPart = new ArrayList<>();
                Set<Expr> thisPartEvs = new HashSet<>();
                for (int i = 0; i < symbolicTups.length; ++i) {
                    if (uf.find(i).equals(thisRoot)) {
                        thisPart.add(bodyClauses[i]);
                        thisPartEvs.addAll(usedEvs.get(i));
                    }
                }

                BoolExpr thisPartConjunction = context.mkAnd(thisPart.toArray(new BoolExpr[0]));
                if (thisPartEvs.isEmpty()) {
                    body.add(thisPartConjunction);
                } else {
                    body.add(context.mkExists(thisPartEvs.toArray(new Expr[0]), thisPartConjunction, 1, null,
                            null, null, null));
                }
            }

//            Map<Integer, Set<Expr>> usedEvs = new HashMap<>();
//            for (int i = 0; i < symbolicTups.length; ++i) {
//                Set<Expr> vs = symbolicTups[i].stream().collect(Collectors.toSet());
//                vs.retainAll(existentialVars);
//                usedEvs.put(i, vs);
//            }
//
//            while (!usedEvs.isEmpty()) {
//                Iterator<Map.Entry<Integer, Set<Expr>>> it = usedEvs.entrySet().iterator();
//                Map.Entry<Integer, Set<Expr>> curr = it.next();
//
//                List<BoolExpr> thisPart = new ArrayList<>();
//                thisPart.add(bodyClauses[curr.getKey()]);
//                Set<Expr> thisPartEvs = new HashSet<>(curr.getValue());
//                it.remove();
//
//                while (it.hasNext()) {
//                    Map.Entry<Integer, Set<Expr>> entry = it.next();
//                    if (!Sets.intersection(curr.getValue(), entry.getValue()).isEmpty()) {
//                        thisPart.add(bodyClauses[entry.getKey()]);
//                        thisPartEvs.addAll(entry.getValue());
//                        it.remove();
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

            if (!predicate.isTrue()) {
                body.add(predicate);
            }

            if (predicate.getSExpr().contains("mdct!")) {
                System.out.println("Naive:");
                System.out.println(naive);
                System.out.println("Split:");
                for (BoolExpr b : body) {
                    System.out.println(b);
                }
                System.out.println("***");
            }
        }

//        BoolExpr bodyFormula = context.mkAnd(context.mkAnd(bodyClauses), predicate);

//        Expr[] evArr = existentialVars.toArray(new Expr[0]);
        Expr[] headSymTupArr = headSymTup.toExprArray();
        return tuple -> {
//            Expr[] newEvArr = new Expr[evArr.length];
//            for (int i = 0; i < evArr.length; ++i) {
//                newEvArr[i] = context.mkFreshConst("e", evArr[i].getSort());
//            }
//
//            BoolExpr newBodyFormula = (BoolExpr) bodyFormula.substitute(evArr, newEvArr)
//                    .substitute(headSymTupArr, tuple.toExprArray()).simplify();
//            if (newEvArr.length == 0) {
//                return newBodyFormula;
//            }
//
//            return context.mkExists(newEvArr, newBodyFormula, 1, null, null, null, null);
            return context.mkAnd(body.stream().map(e -> (BoolExpr) e.substitute(headSymTupArr, tuple.toExprArray()))
                    .toArray(BoolExpr[]::new));
        };
    }

    @Override
    public BoolExpr doesContain(Instance instance, Tuple tuple) {
        // Returns a formula stating that tuple is in the output of this query on the instance.
        return inst2DoesContainTemplate.computeIfAbsent(instance, this::makeDoesContainTemplate).apply(tuple);
//        Tuple[] symbolicTups = relations.stream().map(schema::makeFreshTuple).toArray(Tuple[]::new);
//        BoolExpr predicate = predicateGenerator(symbolicTups);
//        Tuple headSymTup = headSelector(symbolicTups);
//        checkArgument(headSymTup.size() == tuple.size());
//
//        BoolExpr[] bodyExprs = new BoolExpr[relations.size()];
//        for (int i = 0; i < relations.size(); ++i) {
//            String relationName = relations.get(i);
//            Tuple tup = symbolicTups[i];
//            bodyExprs[i] = instance.get(relationName).doesContainExpr(tup);
//        }
//
//        MyZ3Context context = schema.getContext();
//        BoolExpr bodyFormula = context.mkAnd(bodyExprs);
//        Set<Expr> existentialVars = Arrays.stream(symbolicTups).flatMap(Tuple::stream).collect(Collectors.toSet());
//        headSymTup.stream().forEach(existentialVars::remove);
//
//        for (int i = 0; i < tuple.size(); ++i) {
//            bodyFormula = (BoolExpr) bodyFormula.substitute(headSymTup.get(i), tuple.get(i));
//            predicate = (BoolExpr) predicate.substitute(headSymTup.get(i), tuple.get(i));
//        }
//
//        if (existentialVars.isEmpty()) {
//            return context.mkAnd(bodyFormula, predicate);
//        }
//
//        return context.mkExists(existentialVars.toArray(new Expr[0]), context.mkAnd(bodyFormula, predicate), 1, null, null, null, null);
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
        visitJoins(instance, (Tuple[] ts, BoolExpr[] es) -> {
            exprs.add(context.mkAnd(context.mkAnd(es), predicateGenerator(ts)));
        });
        return exprs.toArray(new BoolExpr[0]);
    }

    @Override
    public BoolExpr[] generateExists(Instance instance, Solver solver) {
        checkArgument(instance.isConcrete);

        final MyZ3Context context = instance.getContext();
        final List<BoolExpr> exprs = new ArrayList<>();
        visitJoins(instance, (Tuple[] ts, BoolExpr[] es) -> {
            exprs.add(context.mkAnd(context.mkAnd(es), predicateGenerator(ts)));
        });

        if (solver != null) {
            int numRemoved = 0;
            ListIterator<BoolExpr> it = exprs.listIterator();
            while (it.hasNext()) {
                BoolExpr e = it.next();
                if (solver.check(e) == Status.UNSATISFIABLE) {
                    it.set(context.mkFalse());
                    ++numRemoved;
                }
            }
            System.out.println(numRemoved + " / " + exprs.size());
        }
        return exprs.toArray(new BoolExpr[0]);
    }
}
