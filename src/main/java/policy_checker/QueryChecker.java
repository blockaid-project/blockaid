package policy_checker;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import sql.PrivacyQuery;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;

public class QueryChecker {
    private ArrayList<Policy> policySet;
    private HashMap<Policy, LoadingCache<PrivacyQuery ,Boolean>> policy_decision_cache;

    public QueryChecker(ArrayList<Policy> policySet)
    {
        this.policySet = policySet;
        this.policy_decision_cache = new HashMap<>();
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
            this.policy_decision_cache.put(policy, cache);
        }
    }

    private boolean precheck_policy_approval(PrivacyQuery query) {
        return false;
    }

    private boolean precheck_policy_denial(PrivacyQuery query, Policy policy) {
        return false;
    }

    private boolean check_policy(PrivacyQuery query, Policy policy) {
        if (precheck_policy_denial(query, policy)) {
            return false;
        }
        // todo
        return true;
    }

    public boolean check_policy(PrivacyQuery query) {
        // todo: maybe a cache on precheck?
        if (precheck_policy_approval(query)) {
            return true;
        }

        for(Map.Entry<Policy, LoadingCache<PrivacyQuery, Boolean>> policy_cache: policy_decision_cache.entrySet()){
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
