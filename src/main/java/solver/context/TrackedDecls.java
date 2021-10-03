package solver.context;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

public interface TrackedDecls {
    Iterable<Expr> getConsts();
    Iterable<FuncDecl> getFuncDecls();
}
