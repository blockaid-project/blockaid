package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.Iterables;
import com.microsoft.z3.BoolExpr;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public interface Relation {
    BoolExpr isEmptyExpr();
    Iterable<BoolExpr> doesContainExpr(Tuple tup);
    Iterable<BoolExpr> isContainedInExpr(Relation other);
    Iterable<BoolExpr> equalsExpr(Relation other);

    default Iterable<BoolExpr> doesContainExpr(List<Tuple> other) {
        if (other.isEmpty()) {
            return Collections.emptyList();
        }

        List<BoolExpr> res = new ArrayList<>();
        for (Tuple tup : other) {
            Iterables.addAll(res, doesContainExpr(tup));
        }
        return res;
    }
}
