package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

import java.util.List;

public interface Relation {
    BoolExpr apply(Expr... args);

    BoolExpr apply(Tuple tup);

    BoolExpr doesContain(List<Tuple> other);

    BoolExpr isContainedIn(Relation other);

    BoolExpr equalsExpr(Relation other);
}
