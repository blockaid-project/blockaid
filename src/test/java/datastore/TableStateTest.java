package datastore;

import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql.parser.ddl.SqlDdlParserImpl;

public class TableStateTest {

    public static void TableStateTest(){
        // Check query against table updates
        //CREATE VIEW blah as
        /*String querytest = "CREATE VIEW blah as select PRODUCTID,ORDERID from SORDERS";
        //String querytest = "select PRODUCTID,ORDERID into hello from SORDERS";

        SqlParser.Config sqlParserConfig = SqlParser.configBuilder()
                .setParserFactory(SqlDdlParserImpl.FACTORY)
                .build();
        SqlParser parser = SqlParser.create(querytest, sqlParserConfig);
        SqlNode n = parser.parseStmt();

        TableState datastore = new TableState();
        datastore.insertBaseTable("SORDERS");
        datastore.updateDerivedTables(n);
        System.out.println(datastore.getDerived_tables());*/
    }
}
