package catalog.json;

import org.apache.calcite.DataContext;
import org.apache.calcite.linq4j.tree.Expression;
import org.apache.calcite.linq4j.tree.Expressions;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.util.BuiltInMethod;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;

import com.google.common.collect.ImmutableList;

import planner.MetadataSchema;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.List;


/**
 * An implementation of {@link MetadataSchema}
 * that is constructed from JSON
 */
public class RelSchema extends MetadataSchema {
    private static final Logger LOG = LoggerFactory.getLogger(RelSchema.class);

    public RelSchema() {
        super();
    }

    /* @JsonCreator
    public RelSchema(@JsonProperty("views") List<JsonView> views,
                     @JsonProperty("cubes") List<JsonCube> cubes) {
        super();
    }*/

    @Override
    public Expression getExpression(SchemaPlus parentSchema,
                                    String name) {
        return Expressions.call(
                DataContext.ROOT,
                BuiltInMethod.DATA_CONTEXT_GET_ROOT_SCHEMA.method);
    }

}