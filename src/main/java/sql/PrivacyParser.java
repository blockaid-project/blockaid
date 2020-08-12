package sql;

import org.apache.calcite.adapter.java.JavaTypeFactory;
import org.apache.calcite.avatica.util.Casing;
import org.apache.calcite.avatica.util.Quoting;
import org.apache.calcite.jdbc.CalcitePrepare;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;
import planner.DataSourceSchema;

import java.util.Properties;

public class PrivacyParser implements Parser {

    private final QueryContext context;

    public PrivacyParser(Properties info) throws PrivacyException
    {
        System.out.println("inside constructor");
        this.context = new QueryContext(info);
        System.out.println("in query context");
    }

    public PrivacyParserResult parse(String sql)
    {
        System.out.println("Parsing in privacyparser");
        SqlParser parser = SqlParser.create(sql,
                SqlParser.configBuilder()
                        .setQuotedCasing(Casing.UNCHANGED)
                        .setUnquotedCasing(Casing.UNCHANGED)
                        .setQuoting(Quoting.DOUBLE_QUOTE)
                        .build());
        SqlNode sqlNode;
        try {
            sqlNode = parser.parseStmt();
        } catch (SqlParseException e){
                throw new RuntimeException("parse failed: " + e.getMessage(), e);
        }

        DataSourceSchema datasource = this.context.getDefaultDataSource();

        return new PrivacyParserResult(sql,
                datasource,
                sqlNode.getKind(),
                sqlNode,
                determineCheckability(sqlNode),
                true
                );
    }

    public SchemaPlus getRootSchma(){
        return context.getRootSchema();
    }

    public JavaTypeFactory getTypeFactory() {
        return context.getTypeFactory();
    }

    //Black Box for what is checkable at the moment in the query
    public boolean determineCheckability(SqlNode sqlNode){
        return true;
    }

    public class PrivacyParserResult extends ParserResult{
        private final DataSourceSchema datasource;
        public PrivacyParserResult(String parsedSql,
                                   DataSourceSchema datasource,
                                   SqlKind kind,
                                   SqlNode sqlNode,
                                   boolean isCheckable,
                                   boolean parseResult){
            super(parsedSql, kind, sqlNode, isCheckable, parseResult);
            this.datasource = datasource;
        }

        public DataSourceSchema getDataSource() {
            return datasource;
        }
    }

}



