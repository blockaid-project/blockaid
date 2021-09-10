package cache.unsat_core;

import com.google.common.collect.ImmutableSet;
import solver.MyZ3Context;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;

public abstract class AbstractUnsatCoreEnumerator<L> implements AutoCloseable {
    private Collection<L> labels;
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
                if (order != Order.INCREASING && !isUnsatCoreAlwaysMin()) { // Must shrink.
                    long startMs = System.currentTimeMillis();
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
                    System.out.println("\t\t| Shrink:\t" + (System.currentTimeMillis() - startMs));
                }
                ms.blockUp(currSeed);
                return Optional.of(currSeed);
            }

            // SAT case: grow.
            Set<L> currSeed = satLabels.get();
            if (order != Order.DECREASING) {
                currSeed = grow(currSeed);
            }
            ms.blockDown(currSeed);
        }
        return Optional.empty();
    }

    private Set<L> grow(Set<L> seed) {
        if ((getLabels().size() - seed.size() >= 20) && supportsIsSubsetSatWithBound()) {
            return growBinarySearch(seed);
        } else {
            return growLinear(seed);
        }
    }

    private Set<L> growBinarySearch(Set<L> seed) {
        long startMs = System.currentTimeMillis();
        int lowerBound = seed.size(), upperBound = getLabels().size();
        while (lowerBound < upperBound) {
            int mid = (lowerBound + upperBound + 1) / 2;
            Optional<Set<L>> satLabels = isSubsetSat(seed, mid);
            if (satLabels.isEmpty()) {
                upperBound = mid - 1;
            } else {
                seed = satLabels.get();
                lowerBound = seed.size();
            }
        }
        System.out.println("\t\t| GrowB:\t" + (System.currentTimeMillis() - startMs));
        return seed;
    }

    private Set<L> growLinear(Set<L> seed) {
        long startMs = System.currentTimeMillis();
        Set<L> currSeed = new HashSet<>(seed);
        for (L label : labels) {
            if (currSeed.contains(label)) {
                continue;
            }
            currSeed.add(label);
            Optional<Set<L>> satLabels = isSubsetSat(currSeed);
            if (satLabels.isEmpty()) {
                currSeed.remove(label);
            } else {
                currSeed = satLabels.get();
            }
        }
        System.out.println("\t\t| GrowL:\t" + (System.currentTimeMillis() - startMs));
        return currSeed;
    }

    // From now on, only consider unsat cores within this subset of labels.
    public void restrictTo(Set<L> subset) {
        checkArgument(this.labels.containsAll(subset));
        this.labels = subset;
        ms.restrictTo(subset);
    }

    protected Collection<L> getLabels() {
        return Collections.unmodifiableCollection(labels);
    }

    // If SAT, returns labels for which the formula is SAT.  If UNSAT, returns None.
    protected abstract Optional<Set<L>> isSubsetSat(Set<L> labels);
    protected boolean supportsIsSubsetSatWithBound() {
        return false;
    }
    protected Optional<Set<L>> isSubsetSat(Set<L> labels, int atLeast) {
        throw new UnsupportedOperationException("isSubsetSat with lower bound is not implemented");
    }
    // Called after `isSubsetSat` returns empty.
    protected Optional<Set<L>> getUnsatCore() {
        return Optional.empty();
    }
    // Returns true if getUnsatCore() always returns a minimal unsat core.
    protected boolean isUnsatCoreAlwaysMin() {
        return false;
    }
}
