package sql;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableMultimap;
import com.google.common.collect.ImmutableSet;
import org.apache.calcite.schema.SchemaPlus;
import solver.ForeignKeyDependency;

import java.util.*;

import static com.google.common.base.Preconditions.checkNotNull;

public class SchemaPlusWithKey {
    // FIXME(zhangwen): put all constraints in the schema?
    public final SchemaPlus schema;
    public final ImmutableMap<String, ImmutableList<String>> primaryKeys;
    private final ImmutableSet<ForeignKeyDependency> foreignKeys;

    public SchemaPlusWithKey(SchemaPlus schema,
                             ImmutableMap<String, ImmutableList<String>> primaryKeys,
                             ImmutableSet<ForeignKeyDependency> foreignKeys) {
        this.schema = checkNotNull(schema);
        this.primaryKeys = checkNotNull(primaryKeys);
        this.foreignKeys = checkNotNull(foreignKeys);
    }

    public boolean hasForeignKeyConstraint(String fromTable, String fromColumn, String toTable, String toColumn) {
        // FIXME(zhangwen): the calls to `toUpperCase` are ugly.
        return foreignKeys.contains(new ForeignKeyDependency(
                fromTable.toUpperCase(), fromColumn.toUpperCase(), toTable.toUpperCase(), toColumn.toUpperCase()
        ));
    }
}
