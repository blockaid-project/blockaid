package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;

public interface RelationFunction {
    Iterable<BoolExpr> apply(Expr<?>... args);
}
