package solver;

import com.microsoft.z3.*;

import java.util.List;

public class Relation {
    Function function;

    Sort[] signature;

    public Relation(Function function, Sort[] signature) {
        this.function = function;
        this.signature = signature;
    }

    public BoolExpr apply(Expr... args) {
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
