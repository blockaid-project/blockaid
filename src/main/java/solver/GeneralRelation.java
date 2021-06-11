package solver;

import com.microsoft.z3.*;

import java.util.Arrays;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class GeneralRelation implements Relation {
    private final Schema schema;
    private final Context context;
    private final Function function;
    private final Sort[] signature;

    public GeneralRelation(Schema schema, Function function, Sort[] signature) {
        this.schema = checkNotNull(schema);
        this.context = schema.getContext();
        this.function = checkNotNull(function);
        this.signature = signature;
    }

    @Override
    public BoolExpr apply(Tuple tup) {
        Expr[] args = tup.replaceNullsWithFreshConsts(signature).toExprArray();
        return this.function.apply(args);
    }

    @Override
    public BoolExpr isContainedIn(Relation other) {
        Tuple syms = makeFreshHead();
        BoolExpr lhs = this.apply(syms);
        BoolExpr rhs = other.apply(syms);
        if (syms.isEmpty()) {
            return context.mkImplies(lhs, rhs);
        }
        return context.mkForall(syms.toExprArray(), context.mkImplies(lhs, rhs), 1,
                null, null, null, null);
    }

    private Tuple makeFreshHead() {
        return new Tuple(schema, Arrays.stream(signature).map(sort -> context.mkFreshConst("v", sort)));
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
    public BoolExpr equalsExpr(Relation other) {
        checkArgument(other instanceof GeneralRelation);

        Tuple syms = makeFreshHead();
        BoolExpr lhs = this.apply(syms);
        BoolExpr rhs = other.apply(syms);
        if (syms.isEmpty()) {
            return context.mkEq(lhs, rhs);
        }
        return context.mkForall(syms.toExprArray(), context.mkEq(lhs, rhs), 1, null, null, null, null);
    }
}
