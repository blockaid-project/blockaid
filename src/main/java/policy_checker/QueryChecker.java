package policy_checker;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import sql.PrivacyQuery;

import java.util.*;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;

public class QueryChecker {
    private ArrayList<Policy> policySet;
    private List<Set<String>> preapprovedSets;
    private HashMap<Policy, LoadingCache<PrivacyQuery ,Boolean>> policyDecisionCache;

    private static final int PREAPPROVE_MAX_PASSES = Integer.MAX_VALUE;

    // todo: this
    class Predicate {}

    public QueryChecker(ArrayList<Policy> policySet)
    {
        this.policySet = policySet;
        this.policyDecisionCache = new HashMap<>();
        for (Policy policy : policySet) {
            // Just some random settings
            LoadingCache<PrivacyQuery, Boolean> cache = CacheBuilder.newBuilder()
                    .expireAfterAccess(100000, TimeUnit.SECONDS)
                    .maximumSize(50)
                    .build(new CacheLoader<PrivacyQuery, Boolean>() {
                        @Override
                        public Boolean load(final PrivacyQuery query) {
                            return check_policy(query, policy);
                        }
                    });
            this.policyDecisionCache.put(policy, cache);
        }

        this.preapprovedSets = new ArrayList<>();
        buildPreapprovedSets();
    }

    private void buildPreapprovedSets() {
        // somewhat similar to QO join order DP algorithm in iteration order)
        class Entry {
            private Predicate predicate;
            private Set<String> columns;

            public Entry(Predicate predicate, Set<String> columns) {
                this.predicate = predicate;
                this.columns = columns;
            }
        }

        Map<Set<Integer>, Entry> previousPass = new HashMap<>();
        previousPass.put(Collections.emptySet(), new Entry(new Predicate(), getAllColumns())); // todo: object -> false predicate

        Map<Set<Integer>, Entry> currentPass;

        for (int i = 1; i <= policySet.size() && i <= PREAPPROVE_MAX_PASSES && !previousPass.isEmpty(); ++i) {
            currentPass = new HashMap<>();

            Set<Set<Integer>> remove = new HashSet<>();
            for (Map.Entry<Set<Integer>, Entry> e : previousPass.entrySet()) {
                Set<Integer> prevSet = e.getKey();
                Entry entry = e.getValue();
                Predicate prevPredicate = entry.predicate;
                Set<String> prevColumns = entry.columns;

                for (int j = 0; j < policySet.size(); ++j) {
                    if (prevSet.contains(j)) {
                        continue;
                    }

                    Set<Integer> nextSet = new HashSet<>(prevSet);
                    nextSet.add(j);

                    if (prevPredicate == null) {
                        // previous set was added to preapprovedSet
                        remove.add(nextSet);
                    } else if (!currentPass.containsKey(nextSet)) {
                        Set<String> nextColumns = setIntersection(prevColumns, policySet.get(i).getProjectColumns());

                        if (!nextColumns.isEmpty()) {
                            Predicate nextPredicate = prevPredicate; // todo OR
                            boolean predicateResult = false; // todo: evaluate (predicate OR policy[j].predicate)
                            currentPass.put(nextSet, new Entry(predicateResult ? null : nextPredicate, nextColumns));
                        }
                    }
                }
            }

            for (Set<Integer> s : remove) {
                currentPass.remove(s);
            }

            for (Map.Entry<Set<Integer>, Entry> entry : currentPass.entrySet()) {
                if (entry.getValue().predicate == null) {
                    preapprovedSets.add(entry.getValue().columns);
                }
            }

            previousPass = currentPass;
        }
    }

    private Set<String> getAllColumns() {
        Set<String> r = new HashSet<>();
        for (Policy policy : policySet) {
            r.addAll(policy.getProjectColumns());
        }
        return r;
    }

    private <T> Set<T> setIntersection(Set<T> s1, Set<T> s2) {
        Set<T> sr = new HashSet<>(s1);
        sr.removeAll(s2);
        return sr;
    }

    private boolean containsAll(Collection<String> set, Collection<String> query) {
        return set.containsAll(query);
    }

    private boolean containsAny(Collection<String> set, Collection<String> query) {
        for (String s : query) {
            if (set.contains(s)) {
                return true;
            }
        }
        return false;
    }

    private boolean precheck_policy_approval(PrivacyQuery query) {
        Set<String> projectColumns = query.getProjectColumns();
        for (Set<String> s : preapprovedSets) {
            if (containsAll(s, projectColumns)) {
                return true;
            }
        }
        return false;
    }

    private boolean precheck_policy_denial(PrivacyQuery query, Policy policy) {
        Set<String> projectColumns = query.getProjectColumns();
        return containsAll(policy.getProjectColumns(), projectColumns) && containsAny(policy.getThetaRelations(), projectColumns);
    }

    private boolean check_policy(PrivacyQuery query, Policy policy) {
        if (precheck_policy_denial(query, policy)) {
            return false;
        }
        // todo - full policy check here
        return true;
    }

    public boolean check_policy(PrivacyQuery query) {
        // todo: maybe a cache on precheck?
        if (precheck_policy_approval(query)) {
            return true;
        }

        for(Map.Entry<Policy, LoadingCache<PrivacyQuery, Boolean>> policy_cache: policyDecisionCache.entrySet()){
            boolean compliance;
            try{
                compliance = policy_cache.getValue().get(query);
                if (!compliance) {
                    return false;
                }
            } catch (ExecutionException e){
                throw propagate(e);
            }
        }
        return true;
    }

    private RuntimeException propagate(Throwable e) {
        if (e instanceof RuntimeException) {
            throw (RuntimeException) e;
        } else if (e instanceof Error) {
            throw (Error) e;
        } else {
            throw new RuntimeException(e.getMessage());
        }
    }
}
