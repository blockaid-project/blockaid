package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.enumerations.Z3_sort_kind;

import static com.google.common.base.Preconditions.checkArgument;

public class Z3Function implements Function {
    private final FuncDecl functionDecl;

    public FuncDecl getFunctionDecl() {
        return functionDecl;
    }

    public Z3Function(FuncDecl functionDecl) {
        checkArgument(functionDecl.getRange().getSortKind() == Z3_sort_kind.Z3_BOOL_SORT);
        this.functionDecl = functionDecl;
    }

    @Override
    public BoolExpr apply(Expr... args) {
        return (BoolExpr) functionDecl.apply(args);
    }
}
