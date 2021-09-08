package solver;

import com.microsoft.z3.*;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

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

    @Override
    public BoolExpr doesContainExpr(Tuple tup) {
        Expr[] args = tup.replaceNullsWithFreshConsts(signature).toExprArray();
        return this.function.apply(args);
    }

    @Override
    public BoolExpr isEmptyExpr() {
        Tuple tup = makeFreshHead();
        return context.mkForall(tup.toExprArray(), context.mkNot(doesContainExpr(tup)), 1, null, null, null, null);
    }

    @Override
    public Iterable<BoolExpr> isContainedInExpr(Relation other) {
        Tuple syms = makeFreshHead();
        BoolExpr lhs = this.doesContainExpr(syms);
        BoolExpr rhs = other.doesContainExpr(syms);
        if (syms.isEmpty()) {
            return List.of(context.mkImplies(lhs, rhs));
        }
        return List.of(context.mkForall(syms.toExprArray(), context.mkImplies(lhs, rhs), 1,
                null, null, null, null));
    }

    private Tuple makeFreshHead() {
        return new Tuple(schema, Arrays.stream(signature).map(sort -> context.mkFreshConst("v", sort)));
    }

    @Override
    public Iterable<BoolExpr> doesContainExpr(List<Tuple> other) {
        if (other.isEmpty()) {
            return Collections.emptyList();
        }

        return other.stream().map(this::doesContainExpr).collect(Collectors.toList());
    }

    @Override
    public List<BoolExpr> equalsExpr(Relation other) {
        checkArgument(other instanceof GeneralRelation);

        Tuple syms = makeFreshHead();
        BoolExpr lhs = this.doesContainExpr(syms);
        BoolExpr rhs = other.doesContainExpr(syms);
        if (syms.isEmpty()) {
            return List.of(context.mkEq(lhs, rhs));
        }
        return List.of(context.mkForall(syms.toExprArray(), context.mkEq(lhs, rhs), 1, null, null, null, null));
    }
}
