package planner;

import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.schema.impl.AbstractSchema;

import sql.PrivacyException;

import sql.QueryContext;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Stores name and {@link SchemaPlus} twin for all schemas
 */
public abstract class PrivacySchema extends AbstractSchema {
    private static final Logger LOG = LoggerFactory.getLogger(PrivacySchema.class);

    final String name;
    protected SchemaPlus schemaPlus;
    public PrivacySchema(String name) {
        super();
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public abstract void initialize(QueryContext queryContext, SchemaPlus schemaPlus)
            throws PrivacyException;
}
