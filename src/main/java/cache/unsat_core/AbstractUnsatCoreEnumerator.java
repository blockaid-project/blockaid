package cache.unsat_core;

import com.google.common.collect.ImmutableSet;
import solver.MyZ3Context;

import java.util.*;

public abstract class AbstractUnsatCoreEnumerator<L> {
    private final Collection<L> labels;
    private final MapSolver<L> ms;
    private final Order order;

    public AbstractUnsatCoreEnumerator(MyZ3Context context, Collection<L> labels, Order order) {
        this.labels = labels;
        this.ms = new MapSolver<>(context, labels, order);
        this.order = order;
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
                Optional<Set<L>> unsatCore = getUnsatCore();
                if (unsatCore.isPresent()) {
                    currSeed = unsatCore.get();
                }
                if (order != Order.INCREASING) { // Must shrink.
                    for (L label : seed) {
                        if (!currSeed.remove(label)) {
                            continue;
                        }
                        satLabels = isSubsetSat(currSeed);
                        if (satLabels.isEmpty()) {
                            unsatCore = getUnsatCore();
                            if (unsatCore.isPresent()) {
                                currSeed = unsatCore.get();
                            }
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
            if (order != Order.DECREASING) {
                for (L label : labels) {
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
            }
            ms.blockDown(currSeed);
        }
        return Optional.empty();
    }

    // If SAT, returns labels for which the formula is SAT.  If UNSAT, returns None.
    protected abstract Optional<Set<L>> isSubsetSat(Set<L> labels);
    // Called after `isSubsetSat` returns empty.
    protected Optional<Set<L>> getUnsatCore() {
        return Optional.empty();
    }
}
