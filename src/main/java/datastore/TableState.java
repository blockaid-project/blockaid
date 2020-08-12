package datastore;

import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.SqlSelect;
import org.apache.calcite.sql.ddl.SqlCreateView;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql.parser.ddl.SqlDdlParserImpl;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

public class TableState {
    HashMap<String, ArrayList<HashMap<String, SqlNode>>> derived_tables;
    HashMap<String, String> pk_table;

    public TableState(){
        this.derived_tables = new HashMap<String, ArrayList<HashMap<String, SqlNode>>>();
        this.pk_table = new HashMap<String, String>();
    }

    public void insert_pk(HashMap<String, String> new_pk) {
        this.pk_table.putAll(new_pk);
    }

    // Based on the initial schema, observe the creation of a base table
    public void insertBaseTable(String baseTable){
        derived_tables.put(baseTable, new ArrayList<HashMap<String, SqlNode>>());
    }

    public HashMap<String, ArrayList<HashMap<String, SqlNode>>> getDerived_tables() {
        return this.derived_tables;
    }

    public HashMap<String, String> getPk_Table(){
        return this.pk_table;
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
                //this.derived_tables = new HashMap<String, ArrayList<Pair<String, SqlNode>>>();
                HashMap<String, SqlNode> derived_entry = new HashMap<String, SqlNode>();
                derived_entry.put(new_view, view_select);
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
