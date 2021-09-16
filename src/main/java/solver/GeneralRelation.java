package solver;

import com.microsoft.z3.*;
import solver.context.MyZ3Context;

import java.util.Arrays;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class GeneralRelation implements Relation {
    private final Schema schema;
    private final MyZ3Context context;
    private final RelationFunction function;
    private final Sort[] signature;

    public GeneralRelation(Schema schema, RelationFunction function, Sort[] signature) {
        this.schema = checkNotNull(schema);
        this.context = schema.getContext();
        this.function = checkNotNull(function);
        this.signature = signature;
    }

    RelationFunction getFunction() {
        return function;
    }

    @Override
    public Iterable<BoolExpr> doesContainExpr(Tuple tup) {
        Expr[] args = tup.replaceNullsWithFreshConsts(signature).toExprArray();
        return this.function.apply(args);
    }

    @Override
    public BoolExpr isEmptyExpr() {
        Tuple tup = makeFreshHead();
        return context.myMkForall(tup.toExprArray(), context.mkNot(context.mkAnd(doesContainExpr(tup))));
    }

    @Override
    public Iterable<BoolExpr> isContainedInExpr(Relation other) {
        Tuple syms = makeFreshHead();
        BoolExpr lhs = context.mkAnd(this.doesContainExpr(syms));
        BoolExpr rhs = context.mkAnd(other.doesContainExpr(syms));
        return List.of(
                context.myMkForall(syms.toExprArray(), context.mkImplies(lhs, rhs))
        );
    }

    private Tuple makeFreshHead() {
        return new Tuple(schema, Arrays.stream(signature).map(sort -> context.mkFreshConst("v", sort)));
    }

    @Override
    public List<BoolExpr> equalsExpr(Relation other) {
        checkArgument(other instanceof GeneralRelation);

        Tuple syms = makeFreshHead();
        BoolExpr lhs = context.mkAnd(this.doesContainExpr(syms));
        BoolExpr rhs = context.mkAnd(other.doesContainExpr(syms));
        return List.of(
                context.myMkForall(syms.toExprArray(), context.mkEq(lhs, rhs))
        );
    }
}
