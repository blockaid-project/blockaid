package solver;

import com.microsoft.z3.*;

import java.util.Arrays;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public class Relation {
    private final Schema schema;
    private final Context context;
    private final Function function;
    private final Sort[] signature;

    public Function getFunction() {
        return function;
    }

    public Relation(Schema schema, Function function, Sort[] signature) {
        this.schema = checkNotNull(schema);
        this.context = schema.getContext();
        this.function = checkNotNull(function);
        this.signature = signature;
    }

    public BoolExpr apply(Expr... args) {
        // FIXME(zhangwen): handle SQL NULL properly.
        // Here I'm using a fresh symbol for NULL.  Assuming that we see NULL here only when a previous query returned
        // NULL, this is... safe?  At least not blatantly unsafe.  I need to think through this...
        if (Arrays.asList(args).contains(null)) {
            Expr[] convertedArgs = new Expr[args.length];
            for (int i = 0; i < args.length; ++i) {
                if (args[i] != null) {
                    convertedArgs[i] = args[i];
                } else {
                    convertedArgs[i] = context.mkFreshConst("n", signature[i]);
                }
            }
            args = convertedArgs;
        }
        return this.function.apply(args);
    }

    public BoolExpr apply(Tuple tup) {
        return apply(tup.toExprArray());
    }

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

    public BoolExpr doesContain(List<Tuple> other) {
        if (other.isEmpty()) {
            return context.mkTrue();
        }

        BoolExpr[] syms = other.stream().map(this::apply).toArray(BoolExpr[]::new);
        return context.mkAnd(syms);
    }

    public BoolExpr equalsExpr(Relation other) {
        Tuple syms = makeFreshHead();
        BoolExpr lhs = this.apply(syms);
        BoolExpr rhs = other.apply(syms);
        if (syms.isEmpty()) {
            return context.mkEq(lhs, rhs);
        }
        return context.mkForall(syms.toExprArray(), context.mkEq(lhs, rhs), 1, null, null, null, null);
    }
}
