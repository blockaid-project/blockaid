package solver;

import com.microsoft.z3.*;

import java.util.*;

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
    public BoolExpr apply(Tuple tup) {
        checkArgument(tup.getSchema() == schema);
        tup = tup.replaceNullsWithFreshConsts(signature);
        List<BoolExpr> syms = new ArrayList<>();
        for (int i = 0; i < tuples.length; ++i) {
            syms.add(context.mkAnd(exists[i], tuples[i].equalsExpr(tup)));
        }
        return context.mkOr(syms.toArray(new BoolExpr[0]));
    }

    @Override
    public BoolExpr isEmpty() {
        return context.mkOr(exists);
    }

    @Override
    public BoolExpr doesContain(List<Tuple> other) {
        if (other.isEmpty()) {
            return context.mkTrue();
        }

        BoolExpr[] syms = other.stream().map(this::apply).toArray(BoolExpr[]::new);
        return context.mkAnd(syms);
    }

    @Override
    public BoolExpr isContainedIn(Relation other) {
        checkArgument(other instanceof ConcreteRelation);

        if (tuples.length > CONTAINMENT_USE_QUANTIFIER_THRESHOLD
                || ((ConcreteRelation) other).tuples.length > CONTAINMENT_USE_QUANTIFIER_THRESHOLD) {
            Tuple syms = makeFreshHead();
            BoolExpr lhs = this.apply(syms);
            BoolExpr rhs = other.apply(syms);
            if (syms.isEmpty()) {
                return context.mkImplies(lhs, rhs);
            }
            return context.mkForall(syms.toExprArray(), context.mkImplies(lhs, rhs), 1,
                    null, null, null, null);
        } else {
            BoolExpr[] exprs = new BoolExpr[tuples.length];
            for (int i = 0; i < exprs.length; ++i) {
                exprs[i] = context.mkOr(context.mkNot(exists[i]), other.apply(tuples[i]));
            }

            if (tuples.length == 0) {
                return context.mkTrue();
            }
            return context.mkAnd(exprs);
        }
    }

    private Tuple makeFreshHead() {
        return new Tuple(schema, Arrays.stream(signature).map(sort -> context.mkFreshConst("v", sort)));
    }

    @Override
    public BoolExpr equalsExpr(Relation other) {
        checkArgument(other instanceof ConcreteRelation);
        ConcreteRelation other_ = (ConcreteRelation) other;
        checkArgument(Arrays.equals(this.signature, other_.signature));

        return context.mkAnd(this.isContainedIn(other), other.isContainedIn(this));
    }
}
