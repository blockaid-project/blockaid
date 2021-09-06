package cache.unsat_core;

import com.google.common.collect.ImmutableBiMap;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import solver.MyZ3Context;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class UnsatCoreEnumerator<L> extends AbstractUnsatCoreEnumerator<L> implements AutoCloseable {
    private final Solver solver;
    private final ImmutableMap<L, BoolExpr> label2BoolConst;
    private final ImmutableMap<BoolExpr, L> boolConst2Label;

    private final Set<L> startingUnsatCore;

    // Uses L::toString() as boolean constant names.
    public UnsatCoreEnumerator(MyZ3Context context, Solver solver, Map<L, BoolExpr> labeledExprs, Order order) {
        super(context, labeledExprs.keySet(), order);

        this.solver = solver;
        solver.push();

        ImmutableBiMap.Builder<L, BoolExpr> builder = new ImmutableBiMap.Builder<>();
        for (Map.Entry<L, BoolExpr> entry : labeledExprs.entrySet()) {
            L label = entry.getKey();
            BoolExpr boolConst = context.mkBoolConst(label.toString());
            builder.put(label, boolConst);
            solver.add(context.mkImplies(boolConst, entry.getValue()));
        }
        ImmutableBiMap<L, BoolExpr> bm = builder.build();
        this.label2BoolConst = bm;
        this.boolConst2Label = bm.inverse();

        long startMs = System.currentTimeMillis();
        // The entire formula had better be unsatisfiable; otherwise there is no unsat core!
        checkArgument(solver.check(label2BoolConst.values().toArray(new BoolExpr[0])) == Status.UNSATISFIABLE,
                "to enumerate unsat cores, the formulas must be unsat");
        long durMs = System.currentTimeMillis() - startMs;
//        System.out.println("\t\t| Enumerator check:\t" + durMs);
        this.startingUnsatCore = getUnsatCore().get();
    }

    public Set<L> getStartingUnsatCore() {
        return startingUnsatCore;
    }

    @Override
    protected Optional<Set<L>> isSubsetSat(Set<L> labels) {
        BoolExpr[] boolConsts = labels.stream().map(label2BoolConst::get).toArray(BoolExpr[]::new);
//        long startMs = System.currentTimeMillis();
        Status status = solver.check(boolConsts);
//        System.out.println("\t\t| isSubsetSat:\t" + status + "\t" + (System.currentTimeMillis() - startMs));

        if (status == Status.SATISFIABLE) {
            Model m = solver.getModel();
            // Gather all the labels that are not false in the model.
            Set<L> satLabels = label2BoolConst.entrySet().stream()
                    .filter(e -> !m.eval(e.getValue(), false).isFalse())
                    .map(Map.Entry::getKey)
                    .collect(Collectors.toSet());
            checkState(satLabels.containsAll(labels));
            return Optional.of(satLabels);
        }
        checkState(status == Status.UNSATISFIABLE, "solver returned: " + status);
        return Optional.empty();
    }

    @Override
    protected Optional<Set<L>> getUnsatCore() {
        return Optional.of(
                Arrays.stream(solver.getUnsatCore()).map(boolConst2Label::get).collect(Collectors.toSet())
        );
    }

    @Override
    public void close() {
        solver.pop();
    }
}
