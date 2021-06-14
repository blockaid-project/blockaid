package solver;

import com.microsoft.z3.*;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class ConcreteRelation implements Relation {
    private final Schema schema;
    private final Context context;
    private final Sort[] signature;
    private final Tuple[] tuples;
    private final BoolExpr[] exists;
    private final FuncDecl funcDecl;

    public ConcreteRelation(Schema schema, Sort[] signature, Tuple[] tuples, BoolExpr[] exists) {
        checkArgument(tuples.length == exists.length, "tuples and exists differ in length");

        this.schema = checkNotNull(schema);
        this.context = schema.getContext();
        this.signature = signature;
        this.tuples = tuples;
        this.exists = exists;
        this.funcDecl = context.mkFreshFuncDecl("c", this.signature, context.getBoolSort());
    }

    public Tuple[] getTuples() {
        return tuples;
    }

    public BoolExpr[] getExists() {
        return exists;
    }

    @Override
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

        Tuple tup = new Tuple(schema, args);
        List<BoolExpr> syms = new ArrayList<>();
        for (int i = 0; i < tuples.length; ++i) {
            syms.add(context.mkAnd(exists[i], tuples[i].tupleEqual(tup)));
        }
        return context.mkOr(syms.toArray(new BoolExpr[0]));
    }

    @Override
    public BoolExpr apply(Tuple tup) {
        return apply(tup.toExprArray());
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

        BoolExpr[] exprs = new BoolExpr[tuples.length];
        for (int i = 0; i < exprs.length; ++i) {
            exprs[i] = context.mkOr(context.mkNot(exists[i]), other.apply(tuples[i]));
        }

        if (tuples.length == 0) {
            return context.mkTrue();
        }
        return context.mkAnd(exprs);
    }

    @Override
    public BoolExpr equalsExpr(Relation other) {
        checkArgument(other instanceof ConcreteRelation);
        ConcreteRelation other_ = (ConcreteRelation) other;
        checkArgument(Arrays.equals(this.signature, other_.signature));

        return context.mkAnd(this.isContainedIn(other), other.isContainedIn(this));
    }
}
