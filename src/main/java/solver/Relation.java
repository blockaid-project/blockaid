package solver;

import com.microsoft.z3.BoolExpr;

import java.util.List;

public interface Relation {
    BoolExpr apply(Tuple tup);

    BoolExpr isEmpty();

    BoolExpr doesContain(List<Tuple> other);

    BoolExpr isContainedIn(Relation other);

    BoolExpr equalsExpr(Relation other);
}
