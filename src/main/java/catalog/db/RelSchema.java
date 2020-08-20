package catalog.db;

import org.apache.calcite.DataContext;
import org.apache.calcite.linq4j.tree.Expression;
import org.apache.calcite.linq4j.tree.Expressions;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.util.BuiltInMethod;

import com.google.common.collect.ImmutableList;

import planner.MetadataSchema;
import planner.PrivacyView;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.List;


/**
 * An implementation of {@link MetadataSchema}
 * that is constructed from database
 */
public class RelSchema extends MetadataSchema {
  private static final Logger LOG = LoggerFactory.getLogger(RelSchema.class);

  public RelSchema() {
    super();
    this.views = ImmutableList.of();
  }

  public RelSchema(List<DbView> views) {
    super();
    this.views = new ArrayList<planner.PrivacyView>(views);
  }

  @Override
  public Expression getExpression(SchemaPlus parentSchema,
                                  String name) {
    return Expressions.call(
        DataContext.ROOT,
        BuiltInMethod.DATA_CONTEXT_GET_ROOT_SCHEMA.method);
  }

  /**
   * An implementation of {@link QuarkView}
   * that is constructed from database
   */

  public static class DbView extends PrivacyView {

    public DbView(String name,
                  String viewSql,
                  String table,
                  String schema,
                  String destination) {
      super(name, viewSql, table, ImmutableList.of(destination, schema),
          ImmutableList.of(schema, table));
    }
  }
}
