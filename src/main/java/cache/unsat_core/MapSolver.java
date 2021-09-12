package cache.unsat_core;

import com.google.common.collect.ImmutableBiMap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.*;
import solver.MyZ3Context;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;
import static util.TerminalColor.ANSI_RED;
import static util.TerminalColor.ANSI_RESET;

// For enumerating minimal unsat cores using the MARCO algorithm.
// Adapted from https://github.com/Z3Prover/z3/blob/master/examples/python/mus/marco.py.
class MapSolver<L> {
    private final MyZ3Context context;
    private final Solver solver;
    private final Order order; // Enumerate seeds in increasing order by size?

    private final ImmutableSet<L> allLabels;
    private final ImmutableMap<BoolExpr, L> var2Label;
    private final ImmutableMap<L, BoolExpr> label2Var;

    private int bound;

    public MapSolver(MyZ3Context context, Collection<L> labels, Order order) {
        this.context = context;
        this.solver = context.mkRawSolver();
        this.order = order;

        this.allLabels = ImmutableSet.copyOf(labels);
        ImmutableBiMap.Builder<BoolExpr, L> var2LabelBuilder = new ImmutableBiMap.Builder<>();
        int i = 0;
        for (L label : labels) {
            var2LabelBuilder.put(context.mkBoolConst("x" + i), label);
            i += 1;
        }
        ImmutableBiMap<BoolExpr, L> var2LabelBi = var2LabelBuilder.build();
        this.var2Label = var2LabelBi;
        this.label2Var = var2LabelBi.inverse();

        this.bound = 0;
        if (order == Order.DECREASING) {
            bound = labels.size();
        }
    }

    public Optional<Set<L>> getNextSeed() {
        boolean found = false;
        if (order == Order.INCREASING) {
            while (bound <= allLabels.size()) {
                Status status = solver.check(context.mkAtMost(var2Label.keySet().toArray(new BoolExpr[0]), bound));
                if (status == Status.SATISFIABLE) {
                    found = true;
                    break;
                }
                checkState(status == Status.UNSATISFIABLE, "solver failed");
                bound += 1;
            }
        } else if (order == Order.DECREASING) {
            while (bound >= 0) {
                Status status = solver.check(context.mkAtLeast(var2Label.keySet().toArray(new BoolExpr[0]), bound));
                if (status == Status.SATISFIABLE) {
                    found = true;
                    break;
                }
                checkState(status == Status.UNSATISFIABLE, "solver failed");
                bound -= 1;
            }
        } else {
            found = (solver.check() == Status.SATISFIABLE);
        }

        if (!found) {
            return Optional.empty();
        }

        HashSet<L> seed = new HashSet<>();
        Model m = solver.getModel();
        for (Map.Entry<BoolExpr, L> entry : var2Label.entrySet()) {
            BoolExpr variable = entry.getKey();
            if ((order == Order.INCREASING && m.eval(variable, false).isTrue())
                    || (order != Order.INCREASING && !m.eval(variable, false).isFalse())) {
                seed.add(entry.getValue());
            }
        }
        return Optional.of(seed);
    }

    public void blockDown(Set<L> labels) {
//        System.out.println(ANSI_RED + "blockDown:\t" + labels.size() + ANSI_RESET);
        HashSet<L> complement = new HashSet<>(allLabels);
        complement.removeAll(labels);
        solver.add(context.mkOr(
                complement.stream().map(label2Var::get).toArray(BoolExpr[]::new)
        ));
    }

    public void blockUp(Set<L> labels) {
//        System.out.println(ANSI_RED + "blockUp:\t" + labels.size() + ANSI_RESET);
        solver.add(context.mkOr(
                labels.stream().map(l -> context.mkNot(label2Var.get(l))).toArray(BoolExpr[]::new)
        ));
    }

    public void restrictTo(Set<L> subset) {
        for (L l : allLabels) {
            if (!subset.contains(l)) {
                solver.add(context.mkNot(label2Var.get(l)));
            }
        }
    }

    public void mustContainAll(Collection<L> subset) {
        for (L l : subset) {
            solver.add(label2Var.get(l));
        }
    }
}
