package cache;

import com.google.common.collect.ImmutableBiMap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import solver.MyZ3Context;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class UnsatCoreEnumerator<L> implements AutoCloseable {
    private final Solver solver;
    private final MapSolver<L> ms;
    private final boolean increasingOrder;
    private final ImmutableMap<L, BoolExpr> label2BoolConst;
    private final ImmutableMap<BoolExpr, L> boolConst2Label;

    // Uses L::toString() as boolean constant names.
    public UnsatCoreEnumerator(MyZ3Context context, Solver solver, Map<L, BoolExpr> labeledExprs,
                               boolean increasingOrder) {
        this.ms = new MapSolver<>(context, labeledExprs.keySet(), increasingOrder);
        this.increasingOrder = increasingOrder;

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

        // The entire formula had better be unsatisfiable; otherwise there is no unsat core!
//        System.out.println(ANSI_RED + ANSI_BLUE_BACKGROUND + "Unsat Core Enumerator pre-check start" + ANSI_RESET);
//        checkArgument(solver.check(label2BoolConst.values().toArray(new BoolExpr[0])) == Status.UNSATISFIABLE);
//        System.out.println(ANSI_RED + ANSI_BLUE_BACKGROUND + "Unsat Core Enumerator pre-check end" + ANSI_RESET);
    }

    public Collection<Collection<L>> enumerateAll() {
        ArrayList<Collection<L>> res = new ArrayList<>();
        for (Optional<Set<L>> core = next(); core.isPresent(); core = next()) {
            res.add(core.get());
        }
        return res;
    }

    public Optional<Set<L>> next() {
        Optional<Set<L>> o;
        while ((o = ms.getNextSeed()).isPresent()) {
            ImmutableSet<L> seed = ImmutableSet.copyOf(o.get());
            Optional<Set<L>> satLabels = isSubsetSat(seed);
            if (satLabels.isEmpty()) { // UNSAT.
                Set<L> currSeed = new HashSet<>(seed);
                if (!increasingOrder) { // Must shrink.
                    for (L label : seed) {
                        if (!currSeed.remove(label)) {
                            continue;
                        }
                        satLabels = isSubsetSat(currSeed);
                        if (satLabels.isEmpty()) {
                            currSeed = Arrays.stream(solver.getUnsatCore()).map(boolConst2Label::get).collect(Collectors.toSet());
                        } else {
                            currSeed.add(label);
                        }
                    }
                }
                ms.blockUp(currSeed);
                return Optional.of(currSeed);
            }

            // SAT case: grow.
            Set<L> currSeed = new HashSet<>(satLabels.get());
            for (L label : label2BoolConst.keySet()) {
                if (currSeed.contains(label)) {
                    continue;
                }
                currSeed.add(label);
                satLabels = isSubsetSat(currSeed);
                if (satLabels.isEmpty()) {
                    currSeed.remove(label);
                } else {
                    currSeed = satLabels.get();
                }
            }
            ms.blockDown(currSeed);
        }
        return Optional.empty();
    }

    // If SAT, returns labels for which the formula is SAT.  If UNSAT, returns None.
    private Optional<Set<L>> isSubsetSat(Set<L> labels) {
        BoolExpr[] boolConsts = labels.stream().map(label2BoolConst::get).toArray(BoolExpr[]::new);
        long startMs = System.currentTimeMillis();
        Status status = solver.check(boolConsts);
        System.out.println("\t\t| isSubsetSat:\t" + status + "\t" + (System.currentTimeMillis() - startMs));

        if (status == Status.SATISFIABLE) {
            Model m = solver.getModel();
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
    public void close() {
        solver.pop();
    }
}
