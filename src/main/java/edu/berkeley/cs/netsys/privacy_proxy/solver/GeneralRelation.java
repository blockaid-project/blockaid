package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.Arrays;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class GeneralRelation<C extends Z3ContextWrapper<?, ?, ?, ?>> implements Relation<C> {
    private final Schema<C> schema;
    private final C context;
    private final RelationFunction function;
    private final Sort[] signature;

    public GeneralRelation(Schema<C> schema, RelationFunction function, Sort[] signature) {
        this.schema = checkNotNull(schema);
        this.context = schema.getContext();
        this.function = checkNotNull(function);
        this.signature = signature;
    }

    RelationFunction getFunction() {
        return function;
    }

    @Override
    public Iterable<BoolExpr> doesContainExpr(Tuple<C> tup) {
        Expr<?>[] args = tup.replaceNullsWithFreshConsts(signature).toExprArray();
        return this.function.apply(args);
    }

    @Override
    public BoolExpr isEmptyExpr() {
        Tuple<C> tup = makeFreshQuantifiedHead();
        return context.myMkForall(tup.toExprArray(), context.mkNot(context.mkAnd(doesContainExpr(tup))));
    }

    @Override
    public Iterable<BoolExpr> isContainedInExpr(Relation<C> other) {
        Tuple<C> syms = makeFreshQuantifiedHead();
        BoolExpr lhs = context.mkAnd(this.doesContainExpr(syms));
        BoolExpr rhs = context.mkAnd(other.doesContainExpr(syms));
        return List.of(
                context.myMkForall(syms.toExprArray(), context.mkImplies(lhs, rhs))
        );
    }

    private Tuple<C> makeFreshQuantifiedHead() {
        return new Tuple<>(schema, Arrays.stream(signature).map(sort -> context.mkFreshQuantifiedConst("e", sort)));
    }

    @Override
    public List<BoolExpr> equalsExpr(Relation<C> other) {
        checkArgument(other instanceof GeneralRelation);

        Tuple<C> syms = makeFreshQuantifiedHead();
        BoolExpr lhs = context.mkAnd(this.doesContainExpr(syms));
        BoolExpr rhs = context.mkAnd(other.doesContainExpr(syms));
        return List.of(
                context.myMkForall(syms.toExprArray(), context.mkEq(lhs, rhs))
        );
    }
}
