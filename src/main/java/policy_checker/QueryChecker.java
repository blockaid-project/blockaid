package policy_checker;

import java.util.ArrayList;

public class QueryChecker {

    ArrayList<Policy> policy_set = new ArrayList<Policy>();

    public QueryChecker(ArrayList<Policy> policy_set)
    {
        this.policy_set = policy_set;
    }

    public boolean check_policy(String sql_query)
    {
        return true;
    }


}
