package sql;

import org.apache.calcite.DataContext;
import org.apache.calcite.adapter.java.JavaTypeFactory;
import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.config.CalciteConnectionConfigImpl;
import org.apache.calcite.config.CalciteConnectionProperty;
import org.apache.calcite.jdbc.CalcitePrepare;
import org.apache.calcite.jdbc.CalciteSchema;
import org.apache.calcite.jdbc.JavaTypeFactoryImpl;
import org.apache.calcite.rel.type.RelDataTypeSystem;
import org.apache.calcite.schema.SchemaPlus;

import com.fasterxml.jackson.databind.ObjectMapper;


import com.google.common.collect.ImmutableList;
import org.apache.calcite.tools.RelRunner;
import sql.PrivacyException;
import planner.DataSourceSchema;
import plugin.DataSource;


import planner.DataSourceSchema;
import planner.PrivacySchema;
import planner.MetadataSchema;
import planner.PrivacyFactory;
import planner.PrivacyFactoryResult;
import plugin.DataSource;
//import com.qubole.quark.planner.TestFactory;


import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Properties;

/**
 * Created by amargoor on 10/26/15.
 */
public class QueryContext {

    protected static final Logger LOG = LoggerFactory.getLogger(QueryContext.class);
    private final SchemaPlus rootSchema = CalciteSchema.createRootSchema(true).plus();
    private DataSourceSchema defaultDataSource;
    private boolean unitTestMode;
    private final List<String> defaultSchema;

    public CalciteConnectionConfig getCfg() {
        return cfg;
    }

    private final CalciteConnectionConfig cfg;

    public JavaTypeFactory getTypeFactory() {
        return typeFactory;
    }

    private final JavaTypeFactory typeFactory;

    private List<String> parseDefaultSchema(Properties info) throws IOException, PrivacyException {
        if (info.getProperty("defaultSchema") != null) {
            final ObjectMapper mapper = new ObjectMapper();
            return Arrays.asList(mapper.readValue(info.getProperty("defaultSchema"), String[].class));
        } else if (defaultDataSource != null) {
            DataSource dataSource = defaultDataSource.getDataSource();
            return ImmutableList.of(defaultDataSource.getName(), dataSource.getDefaultSchema());
        } else {
            return ImmutableList.of(MetadataSchema.NAME);
        }
    }

    public QueryContext(Properties info) throws PrivacyException {
        System.out.println("inside query context");
        try {
            Class schemaFactoryClazz = Class.forName(info.getProperty("schemaFactory"));
            if (!info.contains(CalciteConnectionProperty.FUN.camelName())) {
                info.put(CalciteConnectionProperty.FUN.camelName(), "standard,hive");
            }
            this.cfg = new CalciteConnectionConfigImpl(info);
            final RelDataTypeSystem typeSystem =
                    cfg.typeSystem(RelDataTypeSystem.class, RelDataTypeSystem.DEFAULT);
            this.typeFactory = new JavaTypeFactoryImpl(typeSystem);
            this.unitTestMode = Boolean.parseBoolean(info.getProperty("unitTestMode", "false"));

            Object obj = schemaFactoryClazz.newInstance();
            System.out.println("inside schema factory class");
            if (obj instanceof PrivacyFactory) {
                System.out.println("inside privacy factory");
                final PrivacyFactory schemaFactory = (PrivacyFactory) schemaFactoryClazz.newInstance();
                PrivacyFactoryResult factoryResult = schemaFactory.create(info);

                this.defaultDataSource = factoryResult.defaultSchema;
                defaultSchema = parseDefaultSchema(info);
                System.out.println("finished parsing");

                for (DataSourceSchema schema : factoryResult.dataSourceSchemas) {
                    SchemaPlus schemaPlus = rootSchema.add(schema.getName(), schema);
                    System.out.println("adding root schema");
                    schema.initialize(this, schemaPlus);
                    System.out.println("initializing root schema");
                }
                System.out.println("data source schema");

                SchemaPlus metadataPlus = rootSchema.add(factoryResult.metadataSchema.getName(),
                        factoryResult.metadataSchema);
                factoryResult.metadataSchema.initialize(this, metadataPlus);
            } else {
                final TestFactory schemaFactory = (TestFactory) schemaFactoryClazz.newInstance();
                List<PrivacySchema> schemas = schemaFactory.create(info);
                if (info.getProperty("defaultSchema") == null) {
                    throw new PrivacyException(new Throwable("Default schema has to be specified"));
                }
                final ObjectMapper mapper = new ObjectMapper();
                defaultSchema =
                        Arrays.asList(mapper.readValue(info.getProperty("defaultSchema"), String[].class));
                for (PrivacySchema schema : schemas) {
                    SchemaPlus schemaPlus = rootSchema.add(schema.getName(), schema);
                    schema.initialize(this, schemaPlus);
                }
            }
        } catch (ClassNotFoundException | InstantiationException | IllegalAccessException
                | IOException e) {
            throw new PrivacyException(e);
        }
    }

    public SchemaPlus getRootSchema() {
        return rootSchema;
    }

    public List<String> getDefaultSchemaPath() {
        return defaultSchema;
    }

    public SchemaPlus getDefaultSchema() {
        SchemaPlus defaultSchemaPlus = this.rootSchema;
        for (String schemaName : this.defaultSchema) {
            defaultSchemaPlus = defaultSchemaPlus.getSubSchema(schemaName);
        }
        return defaultSchemaPlus;
    }

    public CalcitePrepare.Context getPrepareContext() {
        return new CalcitePrepare.Context() {

            @Override
            public JavaTypeFactory getTypeFactory() {
                return typeFactory;
            }

            @Override
            public CalciteSchema getRootSchema() {
                return CalciteSchema.from(rootSchema);
            }

            @Override
            public CalciteSchema getMutableRootSchema() {
                return null;
            }

            @Override
            public List<String> getDefaultSchemaPath() {
                return defaultSchema;
            }

            @Override
            public CalciteConnectionConfig config() {
                return cfg;
            }

            @Override
            public CalcitePrepare.SparkHandler spark() {
                return CalcitePrepare.Dummy.getSparkHandler(false);
            }

            @Override
            public DataContext getDataContext() {
                return null;
            }

            @Override
            public List<String> getObjectPath() {
                return null;
            }

            @Override
            public RelRunner getRelRunner() {
                return null;
            }
        };
    }

    public DataSourceSchema getDefaultDataSource() {
        return defaultDataSource;
    }

    public boolean isUnitTestMode() {
        return unitTestMode;
    }
}
