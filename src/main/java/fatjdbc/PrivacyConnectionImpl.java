package fatjdbc;

import fatjdbc.impl.PrivacyServer;
import org.apache.calcite.adapter.java.JavaTypeFactory;
import org.apache.calcite.avatica.AvaticaConnection;
import org.apache.calcite.avatica.AvaticaFactory;
import org.apache.calcite.avatica.AvaticaPreparedStatement;
import org.apache.calcite.avatica.InternalProperty;
import org.apache.calcite.avatica.UnregisteredDriver;
import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.config.CalciteConnectionConfigImpl;
import org.apache.calcite.jdbc.CalciteRootSchema;
import org.apache.calcite.jdbc.JavaTypeFactoryImpl;
import org.apache.calcite.rel.type.RelDataTypeSystem;
import org.apache.calcite.schema.SchemaPlus;

import sql.ParserFactory;
import sql.ParserResult;
import sql.PrivacyException;
import sql.PrivacyParser;

import java.sql.SQLException;
import java.util.Properties;

public class PrivacyConnectionImpl extends AvaticaConnection implements PrivacyConnection {
    public final JavaTypeFactory typeFactory;
    public final PrivacyServer server = new PrivacyServer();
    public final ParserFactory parserFactory = new ParserFactory(info);

    protected PrivacyConnectionImpl(PrivacyDriver driver, AvaticaFactory factory, String url,
                                  Properties info, CalciteRootSchema rootSchema,
                                  JavaTypeFactory typeFactory) throws SQLException {
        super(driver, factory, url, info);
        CalciteConnectionConfig cfg = new CalciteConnectionConfigImpl(info);

        if (typeFactory != null) {
            this.typeFactory = typeFactory;
        } else {
            final RelDataTypeSystem typeSystem =
                    cfg.typeSystem(RelDataTypeSystem.class, RelDataTypeSystem.DEFAULT);
            this.typeFactory = new JavaTypeFactoryImpl(typeSystem);
        }

        this.properties.put(InternalProperty.CASE_SENSITIVE, cfg.caseSensitive());
        this.properties.put(InternalProperty.UNQUOTED_CASING, cfg.unquotedCasing());
        this.properties.put(InternalProperty.QUOTED_CASING, cfg.quotedCasing());
        this.properties.put(InternalProperty.QUOTING, cfg.quoting());
    }


    public CalciteConnectionConfig config() {
        return new CalciteConnectionConfigImpl(info);
    }

    @Override
    public PrivacyStatement createStatement(int resultSetType,
                                          int resultSetConcurrency,
                                          int resultSetHoldability) throws SQLException {
        return (PrivacyStatement) super.createStatement(resultSetType,
                resultSetConcurrency, resultSetHoldability);
    }

    @Override
    public AvaticaPreparedStatement prepareStatement(
            String sql,
            int resultSetType,
            int resultSetConcurrency,
            int resultSetHoldability) throws SQLException {
        AvaticaPreparedStatement preparedStatement = (AvaticaPreparedStatement) super
                .prepareStatement(sql,
                        resultSetType, resultSetConcurrency, resultSetHoldability);
        server.addStatement(this, preparedStatement.handle);
        //server.getStatement(preparedStatement.handle).setSignature(signature);
        return preparedStatement;
    }

    public SchemaPlus getRootSchema() throws PrivacyException {
        try {
            return getSqlQueryParser().getRootSchma();
        } catch (SQLException e) {
            throw new RuntimeException("Resetting the connection failed: "
                    + e.getMessage(), e);
        }
    }

    public JavaTypeFactory getTypeFactory() {
        return typeFactory;
    }

    public Properties getProperties() {
        return info;
    }

    // do not make public
    UnregisteredDriver getDriver() {
        return driver;
    }

    public PrivacyParser getSqlQueryParser() throws SQLException, PrivacyException {
        return (PrivacyParser) parserFactory.getParser(info);
    }

    public synchronized ParserResult parse(String sql) throws SQLException, PrivacyException {
        return parserFactory.getParser(info).parse(sql);
    }
}
