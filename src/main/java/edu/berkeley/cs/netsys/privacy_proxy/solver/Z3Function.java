package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.enumerations.Z3_sort_kind;

import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;

public class Z3Function implements RelationFunction {
    private final FuncDecl<BoolSort> functionDecl;

    public FuncDecl<BoolSort> getFunctionDecl() {
        return functionDecl;
    }

    public Z3Function(FuncDecl<BoolSort> functionDecl) {
        this.functionDecl = functionDecl;
    }

    @Override
    public Iterable<BoolExpr> apply(Expr<?>... args) {
        return List.of((BoolExpr) functionDecl.apply(args));
    }
}
