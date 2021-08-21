package cache;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import solver.MyZ3Context;

import java.util.Collection;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.google.common.base.Preconditions.checkState;

public class UnsatCoreEnumerator {
    private final Solver solver;
    private final MapSolver ms;
    private final ImmutableList<BoolExpr> boolLabels;
//    private final ImmutableMap<BoolExpr, Integer> boolLabelToIdx;

    public UnsatCoreEnumerator(MyZ3Context context, Solver solver, Iterable<BoolExpr> boolLabels) {
        this.solver = solver;
        this.boolLabels = ImmutableList.copyOf(boolLabels);
        this.ms = new MapSolver(context, this.boolLabels.size());

//        ImmutableMap.Builder<BoolExpr, Integer> builder = new ImmutableMap.Builder<>();
//        for (int i = 0; i < this.boolLabels.size(); ++i) {
//            builder.put(this.boolLabels.get(i), i);
//        }
//        this.boolLabelToIdx = builder.build();
    }

    public Optional<Collection<BoolExpr>> next() {
        Optional<Set<Integer>> o;
        while ((o = ms.getNextSeed()).isPresent()) {
            Set<Integer> seed = o.get();
            Optional<Set<Integer>> satIndices = isSubsetSat(seed);
            if (satIndices.isEmpty()) { // UNSAT.
                ms.blockUp(seed);
                return Optional.of(
                        seed.stream().map(boolLabels::get).collect(Collectors.toList())
                );
            }

            // SAT case: grow.
            Set<Integer> currSeed = new HashSet<>(satIndices.get());
            for (int i = 0; i < boolLabels.size(); ++i) {
                if (currSeed.contains(i)) {
                    continue;
                }
                currSeed.add(i);
                satIndices = isSubsetSat(currSeed);
                if (satIndices.isEmpty()) {
                    currSeed.remove(i);
                } else {
                    currSeed = satIndices.get();
                }
            }
            ms.blockDown(currSeed);
        }
        return Optional.empty();
    }

    // If SAT, returns label indices for which the formula is SAT.  If UNSAT, returns None.
    private Optional<Set<Integer>> isSubsetSat(Collection<Integer> indices) {
        BoolExpr[] clauses = indices.stream().map(boolLabels::get).toArray(BoolExpr[]::new);
        Status status = solver.check(clauses);
        if (status == Status.SATISFIABLE) {
            Model m = solver.getModel();
            Set<Integer> satIndices = IntStream.range(0, boolLabels.size())
                    .filter(i -> !m.eval(boolLabels.get(i), false).isFalse())
                    .boxed()
                    .collect(Collectors.toSet());
            checkState(satIndices.containsAll(indices));
            return Optional.of(satIndices);
        }
        checkState(status == Status.UNSATISFIABLE, "solver failed");
        return Optional.empty();
    }
}
