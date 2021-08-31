package solver;

import com.microsoft.z3.BoolExpr;

import java.util.List;

public interface Relation {
    BoolExpr isEmptyExpr();
    BoolExpr doesContainExpr(Tuple tup);
    BoolExpr doesContainExpr(List<Tuple> other);
    Iterable<BoolExpr> isContainedInExpr(Relation other);
    Iterable<BoolExpr> equalsExpr(Relation other);
}
