package cache;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.*;
import solver.MyZ3Context;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.google.common.base.Preconditions.checkState;
import static util.TerminalColor.ANSI_RED;
import static util.TerminalColor.ANSI_RESET;

// For enumerating minimal unsat cores using the MARCO algorithm.
// Adapted from https://github.com/Z3Prover/z3/blob/master/examples/python/mus/marco.py.
class MapSolver {
    private final MyZ3Context context;
    private final int numLabels;
    private final Solver solver;
    private final HashSet<Integer> universe;
    private final ImmutableList<BoolExpr> variables;

    private int bound = 0; // Upper bound on the number of true variables.

    public MapSolver(MyZ3Context context, int numLabels) {
        this.context = context;
        this.solver = context.mkRawSolver();
        this.numLabels = numLabels;
        this.universe = IntStream.range(0, numLabels).boxed().collect(Collectors.toCollection(HashSet::new));
        this.variables = IntStream.range(0, numLabels)
                .mapToObj(i -> context.mkBoolConst("x" + i))
                .collect(ImmutableList.toImmutableList());
    }

    // Enumerate in increasing order in size of true variables.
    public Optional<Set<Integer>> getNextSeed() {
        while (bound <= numLabels) {
            Status status = solver.check(context.mkAtMost(variables.toArray(new BoolExpr[0]), bound));
            if (status == Status.SATISFIABLE) {
                break;
            }
//            System.out.println(ANSI_RED + "MapSolver bound failed: " + bound + ANSI_RESET);
            checkState(status == Status.UNSATISFIABLE, "solver failed");
            bound += 1;
        }

        if (bound > numLabels) {
//            System.out.println(ANSI_RED + "MapSolver quitting" + ANSI_RESET);
            return Optional.empty();
        }

        HashSet<Integer> seed = new HashSet<>();
        Model m = solver.getModel();
        for (int i = 0; i < numLabels; ++i) {
            if (!m.eval(variables.get(i), false).isFalse()) {
                seed.add(i);
            }
        }
//        System.out.println(ANSI_RED + "MapSolver returning: " + seed + ANSI_RESET);
        return Optional.of(seed);
    }

    public void blockDown(Collection<Integer> indices) {
//        System.out.println(ANSI_RED + "blockDown:\t" + indices + ANSI_RESET);
        HashSet<Integer> comp = new HashSet<>(universe);
        comp.removeAll(indices); // Complement of indices.
        solver.add(context.mkOr(
                comp.stream().map(variables::get).toArray(BoolExpr[]::new)
        ));
    }

    public void blockUp(Collection<Integer> indices) {
//        System.out.println(ANSI_RED + "blockUp:\t" + indices + ANSI_RESET);
        solver.add(context.mkOr(
                indices.stream().map(i -> context.mkNot(variables.get(i))).toArray(BoolExpr[]::new)
        ));
    }
}
