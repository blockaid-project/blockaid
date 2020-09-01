package policy_checker;

import sql.PrivacyQuery;

import java.util.ArrayList;

public class QueryChecker {

    private ArrayList<Policy> policySet;

    public QueryChecker(ArrayList<Policy> policySet)
    {
        this.policySet = policySet;
    }

    public boolean check_policy(PrivacyQuery query, Policy p)
    {
        assert policySet.contains(p);
        return true;
    }


}
