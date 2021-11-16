package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.Iterables;
import com.microsoft.z3.BoolExpr;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public interface Relation<C extends Z3ContextWrapper<?, ?, ?, ?>> {
    Iterable<BoolExpr> isEmptyExpr();
    Iterable<BoolExpr> doesContainExpr(Tuple<C> tup);
    Iterable<BoolExpr> isContainedInExpr(Relation<C> other);
    Iterable<BoolExpr> equalsExpr(Relation<C> other);

    default Iterable<BoolExpr> doesContainExpr(List<Tuple<C>> other) {
        if (other.isEmpty()) {
            return Collections.emptyList();
        }

        List<BoolExpr> res = new ArrayList<>();
        for (Tuple<C> tup : other) {
            Iterables.addAll(res, doesContainExpr(tup));
        }
        return res;
    }
}
