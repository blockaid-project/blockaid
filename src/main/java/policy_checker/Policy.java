package policy_checker;

import javafx.util.Pair;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.RelBuilder;

import java.util.ArrayList;

public class Policy {

    ArrayList<RelNode> sql_policies;

    // Temporarily Hard-coded to simple attribute {Name, Attribute, Salary}
    public Policy(ArrayList<RelNode> sql_policies){
        this.sql_policies = sql_policies;
    }

    public static void generate_all_relations(String[] attributes) {

    }

    public ArrayList<Pair<Integer, Integer>> applicable_relations(){

        return new ArrayList<Pair<Integer, Integer>>();
    }

    public boolean check_policy(String query)
    {
        // Generate all versions of the tables


        return true;
    }

}
