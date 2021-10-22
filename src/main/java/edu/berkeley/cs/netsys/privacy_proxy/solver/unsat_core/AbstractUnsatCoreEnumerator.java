package edu.berkeley.cs.netsys.privacy_proxy.solver.unsat_core;

import edu.berkeley.cs.netsys.privacy_proxy.solver.context.MyZ3Context;

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
            Optional<Set<L>> oUnsatCore = processSeed(o.get());
            if (oUnsatCore.isPresent()) {
                return oUnsatCore;
            }
        }
        return Optional.empty();
    }

    // Returns unsat core if seed is unsat, empty otherwise.  Updates unexplored region.
    protected Optional<Set<L>> processSeed(Set<L> seed) {
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
        return Optional.empty();
    }

    private Set<L> grow(Set<L> seed) {
        if ((getLabels().size() - seed.size() >= 20) && supportsIsSubsetSatWithBound()) {
            return growBinarySearch(seed);
        } else {
            return growLinear(seed);
        }
    }

    // Assumes that seed is satisfiable.
    private Set<L> growBinarySearch(Set<L> seed) {
        long startNs = System.nanoTime();
        int lowerBound = seed.size(), upperBound = getLabels().size();
        while (lowerBound < upperBound) {
            int mid = (lowerBound + upperBound + 1) / 2;
            if (isSubsetSatExists(seed, mid)) {
                lowerBound = mid;
            } else {
                upperBound = mid - 1;
            }
        }
        Optional<Set<L>> satLabels = isSubsetSat(seed, lowerBound);
        System.out.println("\t\t| GrowB:\t" + (System.nanoTime() - startNs) / 1000000);
        return satLabels.get();
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

    // Finds critical clauses and constrain all subsets searched to contain them.
    public void optimizeCritical() {
        HashSet<L> currSubset = new HashSet<>(labels);
        ArrayList<L> critical = new ArrayList<>();
        for (L label : labels) {
            currSubset.remove(label);
            // If removing this label alone makes the formula SAT, this label is critical.
            if (isSubsetSat(currSubset).isPresent()) {
                critical.add(label);
            }
            currSubset.add(label);
        }
        System.out.println("critical clauses: " + critical.size() + " / " + labels.size());
        ms.mustContainAll(critical);
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

    /**
     * Checks if there exists a satisfiable subset that (1) contains specified labels and (2) has specified minimum size.
     * @param labels labels that the unsat core must contain.
     * @param atLeast minimum size.
     * @return true if such satisfiable subset exists.
     */
    protected boolean isSubsetSatExists(Set<L> labels, int atLeast) {
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
