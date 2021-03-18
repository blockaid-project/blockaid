package solver;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

public class Z3Function implements Function {
    FuncDecl functionDecl;

    public Z3Function(FuncDecl functionDecl) {
        this.functionDecl = functionDecl;
    }

    @Override
    public Expr apply(Expr... args) {
        return functionDecl.apply(args);
    }
}
