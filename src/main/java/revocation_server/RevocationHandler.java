package revocation_server;

import datastore.TableState;
import org.apache.calcite.sql.SqlDialect;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.util.SqlString;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

public class RevocationHandler {

    TableState derived_tables;
    SqlDialect dialect;

    public RevocationHandler(TableState derived_table, SqlDialect dialect) {
        this.derived_tables = derived_table;
        this.dialect = dialect;
    }

    public ArrayList<SqlString> revokePk(String primary_key)
    {
        String base_table = derived_tables.getPk_Table().get(primary_key);
        ArrayList<HashMap<String, SqlNode>> affected_tables =
                derived_tables.getDerived_tables().get(base_table);

        ArrayList<SqlString> modification_queries = new ArrayList<>();
        for (int i = 0; i < affected_tables.size(); i++){
            HashMap<String, SqlNode> affected_table = affected_tables.get(i);
            Map.Entry<String, SqlNode> entry = affected_table.entrySet().iterator().next();
            if (isTableAffected(entry))
            {
                SqlNode query = modifyTable(entry.getKey(), entry.getValue());
                modification_queries.add(query.toSqlString(dialect));
            }
            else{
                continue;
            }
        }
        return modification_queries;
    }

    // Todo: Wen Blackbox
    public boolean isTableAffected(Map.Entry<String, SqlNode> entry)
    {
        return true;
    }

    // Todo: Generate query to modify result
    // For now, just re-run the query from the base table
    public SqlNode modifyTable(String table_name, SqlNode query)
    {
        return query;
    }

}
