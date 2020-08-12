package planner;

import org.apache.calcite.DataContext;
import org.apache.calcite.linq4j.tree.Expression;
import org.apache.calcite.linq4j.tree.Expressions;
import org.apache.calcite.schema.Schema;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.util.BuiltInMethod;

import com.google.common.collect.ImmutableMap;

import sql.PrivacyException;

import plugin.DataSource;
import plugin.DataSourceFactory;

import sql.QueryContext;

import java.util.Map;

/**
 * Stores sub-schemas read from a {@link DataSource}.
 * It never holds any tables.
 */
public abstract class DataSourceSchema extends PrivacySchema {
    public final Map<String, Object> properties;
    protected ImmutableMap<String, Schema> subSchemaMap;
    private final DataSourceFactory dataSourceFactory;
    private DataSource dataSource = null;

    public DataSourceSchema(Map<String, Object> properties) {
        super((String) properties.get("name"));
        this.properties = properties;
        final String factoryPath = (String) properties.get("factory");
        if (factoryPath == null) {
            throw new RuntimeException("Specify attribute in user "
                    + "JSON input - 'factory': <ClassPath of DataSourceFactory Implemented>");
        }
        try {
            Class dsFactoryClazz = Class.forName(factoryPath);
            this.dataSourceFactory =
                    (DataSourceFactory) dsFactoryClazz.newInstance();
        } catch (Exception e) {
            throw new RuntimeException("Error parsing JSON attribute 'factory': " + e.getMessage(), e);
        }
    }

    @Override
    protected Map<String, Schema> getSubSchemaMap() {
        return subSchemaMap;
    }

    public DataSource getDataSource() throws PrivacyException {
        if (dataSource == null) {
            dataSource = dataSourceFactory.create(properties);
        }
        return dataSource;
    }

    @Override
    public void initialize(QueryContext queryContext, SchemaPlus schemaPlus) throws PrivacyException {
        System.out.println("trying to initialize");
        System.out.println(this.getDataSource().getClass());
        subSchemaMap = this.getDataSource().getSchemas();
        System.out.print("Trying to initialize2");
        this.schemaPlus = schemaPlus;
        for (Map.Entry<String, Schema> entry : subSchemaMap.entrySet()) {

            SchemaPlus subSchemaPlus = this.schemaPlus.add(entry.getKey(), entry.getValue());
            PrivacySchema privacySchema = (PrivacySchema) entry.getValue();

            privacySchema.initialize(queryContext, subSchemaPlus);
        }
    }

    @Override
    public Expression getExpression(SchemaPlus parentSchema,
                                    String name) {
        return Expressions.call(
                DataContext.ROOT,
                BuiltInMethod.DATA_CONTEXT_GET_ROOT_SCHEMA.method);
    }
}
