package sql;

import org.apache.calcite.adapter.java.JavaTypeFactory;
import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.config.Lex;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql.SqlDialect;
import org.apache.calcite.sql.util.SqlShuttle;
import org.apache.calcite.sql.SqlIdentifier;

import org.apache.calcite.sql.validate.SqlConformance;
import org.apache.calcite.sql.validate.SqlConformanceEnum;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import planner.DataSourceSchema;


import java.sql.SQLException;
import java.util.Properties;

public class PrivacyParser implements Parser {

    private static final Logger LOG = LoggerFactory.getLogger(PrivacyParser.class);
    private final QueryContext context;

    public PrivacyParser(QueryContext ctx)
    {
       this.context = ctx;
    }

    public ParserResult parse(String sql) throws SQLException {
        DataSourceSchema dataSource = this.context.getDefaultDataSource();

        final CalciteConnectionConfig config = context.getCfg();
        // Changnote: may need to change conformance of the parser when switching to a different data source
        SqlParser parser = SqlParser.create(sql,
                SqlParser.configBuilder()
                        .setQuotedCasing(config.quotedCasing())
                        .setUnquotedCasing(config.unquotedCasing())
                        .setQuoting(config.quoting())
                        .setLex(Lex.MYSQL)
                        .build());
        SqlNode sqlNode;
        try {
            sqlNode = parser.parseStmt();
        } catch (SqlParseException e){
            throw new RuntimeException("parse failed: " + e.getMessage(), e);
        }

        return new ParserResult(sqlNode);
    }

    public SqlParser getSqlParser(String sql) {
        try {
            final CalciteConnectionConfig config = context.getCfg();
            return SqlParser.create(sql,
                    SqlParser.configBuilder()
                            .setQuotedCasing(config.quotedCasing())
                            .setUnquotedCasing(config.unquotedCasing())
                            .setQuoting(config.quoting())
                            .build());
        } catch (Exception e) {
            return SqlParser.create(sql);
        }
    }

    public SchemaPlus getRootSchma(){
        return context.getRootSchema();
    }

    public JavaTypeFactory getTypeFactory() {
        return context.getTypeFactory();
    }
}



