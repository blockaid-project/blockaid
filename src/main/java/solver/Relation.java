package solver;

import com.microsoft.z3.*;

import java.util.Arrays;
import java.util.List;

public class Relation {
    // TODO(zhangwen): We can now remove the "context" argument from the methods, right?
    Context context;
    Function function;
    Sort[] signature;

    public Relation(Context context, Function function, Sort[] signature) {
        this.context = context;
        this.function = function;
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
        Expr expr = this.function.apply(args);
        assert expr instanceof BoolExpr;
        return (BoolExpr) expr;
    }

    public BoolExpr isContainedIn(Context context, Relation other) {
        Expr[] syms = new Expr[signature.length];
        for (int i = 0; i < signature.length; ++i) {
            syms[i] = context.mkFreshConst("v", signature[i]);
        }
        BoolExpr lhs = this.apply(syms);
        BoolExpr rhs = other.apply(syms);
        return context.mkForall(syms, context.mkImplies(lhs, rhs), 1, null, null, null, null);
    }

//    public BoolExpr isContainedIn(List<Tuple> other) {
//
//    }

    public BoolExpr doesContain(Context context, Relation other) {
        return other.isContainedIn(context, this);
    }

    public BoolExpr doesContain(Context context, List<Tuple> other) {
        BoolExpr[] syms = new BoolExpr[other.size()];
        for (int i = 0; i < other.size(); ++i) {
            syms[i] = this.apply(other.get(i).toArray(new Expr[0]));
        }
        return context.mkAnd(syms);
    }

    public BoolExpr equalsExpr(Context context, Relation other) {
        Expr[] syms = new Expr[signature.length];
        for (int i = 0; i < signature.length; ++i) {
            syms[i] = context.mkFreshConst("v", signature[i]);
        }
        BoolExpr lhs = this.apply(syms);
        BoolExpr rhs = other.apply(syms);
        return context.mkForall(syms, context.mkEq(lhs, rhs), 1, null, null, null, null);
    }
}
