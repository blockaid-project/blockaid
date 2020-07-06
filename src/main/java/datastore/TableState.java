package datastore;

import javafx.util.Pair;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.SqlSelect;
import org.apache.calcite.sql.ddl.SqlCreateView;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql.parser.ddl.SqlDdlParserImpl;

import java.util.ArrayList;
import java.util.HashMap;

public class TableState {
    HashMap<String, ArrayList<Pair<String, SqlNode>>> derived_tables;

    public TableState(){
        this.derived_tables = new HashMap<String, ArrayList<Pair<String, String>>>();
    }

    // Updates Derived Tables if applicable
    public boolean updateDerivedTables(SqlNode node) {
        SqlKind query_kind = node.getKind();
        if (query_kind.equals(SqlKind.CREATE_VIEW))
        {
            String new_view = ((SqlCreateView) node).operand(0).toString();
            SqlSelect view_select = ((SqlCreateView) node).operand(2);
            String basetable = view_select.getFrom().toString();
            if (derived_tables.get(basetable) != null) {
                Pair<String, SqlNode> derived_entry = new Pair(new_view, view_select);
                derived_tables.get(basetable).add(derived_entry);
            }
            else{throw new RuntimeException("Base table not registered inside system");}
            return true;
        }
        else {
            return false;
        }


    }
}
