package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

import java.util.List;

public record Z3Function(FuncDecl<BoolSort> functionDecl) implements RelationFunction {
    @Override
    public Iterable<BoolExpr> apply(Expr<?>... args) {
        return List.of((BoolExpr) functionDecl.apply(args));
    }
}
