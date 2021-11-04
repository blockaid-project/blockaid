package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Sort;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.CONTAINMENT_USE_QUANTIFIER_THRESHOLD;

public class ConcreteRelation<C extends Z3ContextWrapper<?, ?, ?, ?>> implements Relation<C> {
    private final Schema<C> schema;
    private final C context;
    private final ImmutableList<Sort> signature;
    private final ImmutableList<Tuple<C>> tuples;
    private final ImmutableList<BoolExpr> exists;

    public ConcreteRelation(Schema<C> schema, List<Sort> signature, List<Tuple<C>> tuples, List<BoolExpr> exists) {
        checkArgument(tuples.size() == exists.size(), "tuples and exists differ in length");

        this.schema = checkNotNull(schema);
        this.context = schema.getContext();
        this.signature = ImmutableList.copyOf(signature);
        this.tuples = ImmutableList.copyOf(tuples);
        this.exists = ImmutableList.copyOf(exists);
    }

    public ImmutableList<Tuple<C>> getTuples() {
        return tuples;
    }

    public ImmutableList<BoolExpr> getExists() {
        return exists;
    }

    @Override
    public Iterable<BoolExpr> doesContainExpr(Tuple<C> tup) {
        checkArgument(tup.getSchema() == schema);
        tup = tup.fillNulls(signature);
        List<BoolExpr> syms = new ArrayList<>();
        for (int i = 0; i < tuples.size(); ++i) {
            BoolExpr tupEq = tuples.get(i).equalsExpr(tup);
            if (!tupEq.isFalse()) {
                syms.add(context.mkAnd(exists.get(i), tupEq));
            }
        }
        return List.of(context.mkOr(syms.toArray(new BoolExpr[0])));
    }

    @Override
    public BoolExpr isEmptyExpr() {
        return context.mkNot(context.mkOr(exists));
    }

    @Override
    public Iterable<BoolExpr> isContainedInExpr(Relation<C> other) {
        checkArgument(other instanceof ConcreteRelation<C>);
//        if (tuples.length > 10) {
//            System.out.println("*** isContainedInExpr: " + tuples.length);
//        }

        if (tuples.size() > CONTAINMENT_USE_QUANTIFIER_THRESHOLD
                || ((ConcreteRelation<C>) other).tuples.size() > CONTAINMENT_USE_QUANTIFIER_THRESHOLD) {
            Tuple<C> syms = makeFreshHead();
            BoolExpr lhs = context.mkAnd(this.doesContainExpr(syms));
            BoolExpr rhs = context.mkAnd(other.doesContainExpr(syms));
            return List.of(context.myMkForall(syms.toExprArray(), context.mkImplies(lhs, rhs)));
        } else {
            ArrayList<BoolExpr> exprs = new ArrayList<>();
            for (int i = 0; i < exists.size(); ++i) {
                exprs.add(context.mkOr(context.mkNot(exists.get(i)), context.mkAnd(other.doesContainExpr(tuples.get(i)))));
            }
            return exprs;
        }
    }

    private Tuple<C> makeFreshHead() {
        return new Tuple<>(schema, signature.stream().map(sort -> context.mkFreshConst("v", sort)));
    }

    @Override
    public Iterable<BoolExpr> equalsExpr(Relation<C> other) {
        checkArgument(other instanceof ConcreteRelation<C>);
        ConcreteRelation<C> other_ = (ConcreteRelation<C>) other;
        checkArgument(this.signature.equals(other_.signature));

        return Iterables.concat(this.isContainedInExpr(other), other.isContainedInExpr(this));
    }
}
