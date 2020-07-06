package policy_checker;

import javafx.util.Pair;
import org.apache.calcite.rel.RelNode;

import java.util.ArrayList;

public class Policy {

    RelNode[] policy_list;

    public Policy(RelNode[] policy_list){
        this.policy_list = policy_list;
    }

    public ArrayList<Pair<Integer, Integer>> applicable_relations(){
        return new ArrayList<Pair<Integer, Integer>>();
    }

    public boolean check_query_policy(String query)
    {
        // Generate all versions of the tables
        return true;
    }


}
