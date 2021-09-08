package solver;

import com.google.common.collect.Iterables;
import com.google.common.collect.Streams;
import com.microsoft.z3.*;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class ConcreteRelation implements Relation {
    private final Schema schema;
    private final MyZ3Context context;
    private final Sort[] signature;
    private final Tuple[] tuples;
    private final BoolExpr[] exists;

    /* If relation size is greater than this threshold, containment uses quantifiers. */
    private static final int CONTAINMENT_USE_QUANTIFIER_THRESHOLD = Integer.parseInt(System.getProperty("privoxy.containment_use_quantifier_threshold", Integer.toString(Integer.MAX_VALUE)));

    public ConcreteRelation(Schema schema, Sort[] signature, Tuple[] tuples, BoolExpr[] exists) {
        checkArgument(tuples.length == exists.length, "tuples and exists differ in length");

        this.schema = checkNotNull(schema);
        this.context = schema.getContext();
        this.signature = signature;
        this.tuples = tuples;
        this.exists = exists;
    }

    public Tuple[] getTuples() {
        return tuples;
    }

    public BoolExpr[] getExists() {
        return exists;
    }

    @Override
    public Iterable<BoolExpr> doesContainExpr(Tuple tup) {
        checkArgument(tup.getSchema() == schema);
        tup = tup.replaceNullsWithFreshConsts(signature);
        List<BoolExpr> syms = new ArrayList<>();
        for (int i = 0; i < tuples.length; ++i) {
            BoolExpr tupEq = tuples[i].equalsExpr(tup);
            if (!tupEq.isFalse()) {
                syms.add(context.mkAnd(exists[i], tupEq));
            }
        }
        return List.of(context.mkOr(syms.toArray(new BoolExpr[0])));
    }

    @Override
    public BoolExpr isEmptyExpr() {
        return context.mkNot(context.mkOr(exists));
    }

    @Override
    public Iterable<BoolExpr> isContainedInExpr(Relation other) {
        checkArgument(other instanceof ConcreteRelation);
//        if (tuples.length > 10) {
//            System.out.println("*** isContainedInExpr: " + tuples.length);
//        }

        if (tuples.length > CONTAINMENT_USE_QUANTIFIER_THRESHOLD
                || ((ConcreteRelation) other).tuples.length > CONTAINMENT_USE_QUANTIFIER_THRESHOLD) {
            Tuple syms = makeFreshHead();
            BoolExpr lhs = context.mkAnd(this.doesContainExpr(syms));
            BoolExpr rhs = context.mkAnd(other.doesContainExpr(syms));
            if (syms.isEmpty()) {
                return List.of(context.mkImplies(lhs, rhs));
            }
            return List.of(context.mkForall(syms.toExprArray(), context.mkImplies(lhs, rhs), 1,
                    null, null, null, null));
        } else {
            ArrayList<BoolExpr> exprs = new ArrayList<>();
            for (int i = 0; i < exists.length; ++i) {
                exprs.add(context.mkOr(context.mkNot(exists[i]), context.mkAnd(other.doesContainExpr(tuples[i]))));
            }
            return exprs;
        }
    }

    private Tuple makeFreshHead() {
        return new Tuple(schema, Arrays.stream(signature).map(sort -> context.mkFreshConst("v", sort)));
    }

    @Override
    public Iterable<BoolExpr> equalsExpr(Relation other) {
        checkArgument(other instanceof ConcreteRelation);
        ConcreteRelation other_ = (ConcreteRelation) other;
        checkArgument(Arrays.equals(this.signature, other_.signature));

        return Iterables.concat(this.isContainedInExpr(other), other.isContainedInExpr(this));
    }
}
