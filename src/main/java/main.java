import org.apache.calcite.config.Lex;
import org.apache.calcite.jdbc.CalciteConnection;
import org.apache.calcite.jdbc.JavaTypeFactoryImpl;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.type.RelDataTypeFactory;
import org.apache.calcite.rel.type.RelDataTypeSystem;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.schema.Table;
import org.apache.calcite.sql.SqlCreate;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.SqlSelect;
import org.apache.calcite.sql.ddl.SqlCreateView;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql.parser.ddl.SqlDdlParserImpl;
import org.apache.calcite.sql.type.SqlTypeFactoryImpl;
import org.apache.calcite.sql.validate.SqlConformanceEnum;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.RelBuilder;

import policy_checker.Policy;
import sql.QueryParserUtils;

import java.sql.*;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Properties;

public class main {

    public static void main(String[] args) throws Exception {
        new main().run();
    }

    public void run() throws ClassNotFoundException, SQLException, SqlParseException
    {
        // Set up a JDBC Connection for Calcite
        Class.forName("org.apache.calcite.jdbc.Driver");
        Properties info = new Properties();
        //info.setProperty("lex", "JAVA");
        Connection connection =
                DriverManager.getConnection("jdbc:calcite:model="
                        + "/Users/michaelchang/privacy_proxy/src/main/java/model_file.json", info);
        CalciteConnection calciteConnection =
                connection.unwrap(CalciteConnection.class);

        Table t = calciteConnection.getRootSchema().getSubSchema("CUSTOM_TABLE")
                .getTable("SORDERS");
        List attributes = t.getRowType(new JavaTypeFactoryImpl(RelDataTypeSystem.DEFAULT))
                .getFieldNames();

        // Create Policy, expressed as a Relation Builder
        final FrameworkConfig config = (FrameworkConfig) Frameworks.newConfigBuilder()
                .defaultSchema(calciteConnection.getRootSchema()
                        .getSubSchema("CUSTOM_TABLE")).build();
        final RelBuilder builder = RelBuilder.create(config);
        final RelNode node = builder
                .scan("SORDERS")
                .build();
        final RelNode node2 = builder
                .scan("SORDERS")
                .project(builder.field("PRODUCTID"))
                .build();

        RelNode[] policy_nodes = new RelNode[]{node, node2};
        Policy p = new Policy(policy_nodes);
        ArrayList<Policy> policy_set = new ArrayList<Policy>();
        policy_set.add(p);

        // Check query against policy
        String query = "select PRODUCTID from SORDERS";
        boolean isCompliant = true;
        for (Policy policy: policy_set) {
            if (!policy.check_query_policy(query)){
                   isCompliant = false;
                   break;
            }
        }

        // Check query against table updates
        //CREATE VIEW blah as
        String querytest = "CREATE VIEW blah as select PRODUCTID,ORDERID from SORDERS";
        //String querytest = "select PRODUCTID,ORDERID into hello from SORDERS";
        SqlParser.Config sqlParserConfig = SqlParser.configBuilder()
                .setParserFactory(SqlDdlParserImpl.FACTORY)
                .build();
        SqlParser parser = SqlParser.create(querytest, sqlParserConfig);
        SqlNode n = parser.parseStmt();

        System.out.println(n.getKind());
        System.out.println(((SqlCreateView) n).getOperandList());
        SqlSelect test = ((SqlCreateView) n).operand(2);
        System.out.println(test.getFrom());

        //final SqlNode sqlNode = parser.parseStmt();
        //final List<String> tables = QueryParserUtils.extractTableAliases(sqlNode);
        //System.out.println(tables);


        Statement statement = calciteConnection.createStatement();
        ResultSet resultSet = statement.executeQuery(query);


        resultSet.close();
        statement.close();
        connection.close();
    }
}
