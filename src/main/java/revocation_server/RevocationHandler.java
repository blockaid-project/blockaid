package revocation_server;

import datastore.TableState;
import javafx.util.Pair;
import org.apache.calcite.sql.SqlDialect;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.util.SqlString;

import java.util.ArrayList;

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
        ArrayList<Pair<String, SqlNode>> affected_tables =
                derived_tables.getDerived_tables().get(base_table);

        ArrayList<SqlString> modification_queries = new ArrayList<>();
        for (int i = 0; i < affected_tables.size(); i++){
            Pair<String, SqlNode> affected_table = affected_tables.get(i);
            if (isTableAffected(affected_table.getKey(), affected_table.getValue()))
            {
                SqlNode query = modifyTable(affected_table.getKey(), affected_table.getValue());
                modification_queries.add(query.toSqlString(dialect));
            }
            else{
                continue;
            }
        }
        return modification_queries;
    }

    // Todo: Wen Blackbox
    public boolean isTableAffected(String table_name, SqlNode query)
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
