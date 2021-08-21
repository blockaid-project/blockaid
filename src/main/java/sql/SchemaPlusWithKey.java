package sql;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import org.apache.calcite.schema.SchemaPlus;
import solver.ForeignKeyDependency;

import java.util.HashSet;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public class SchemaPlusWithKey {
    // FIXME(zhangwen): put all constraints in the schema?
    public final SchemaPlus schema;
    public final ImmutableMap<String, ImmutableList<String>> primaryKeys;
    private final ImmutableSet<ForeignKeyDependency> foreignKeys;

    // Every column that stores values of a primary key type (e.g., a PK column, or a foreign key to a PK column).
    private final ImmutableSet<String> pkValuedColumns;

    public SchemaPlusWithKey(SchemaPlus schema,
                             ImmutableMap<String, ImmutableList<String>> primaryKeys,
                             ImmutableSet<ForeignKeyDependency> foreignKeys) {
        this.schema = checkNotNull(schema);
        this.primaryKeys = checkNotNull(primaryKeys);
        this.foreignKeys = checkNotNull(foreignKeys);

        HashSet<String> pkValuedColumns = new HashSet<>();
        for (Map.Entry<String, ImmutableList<String>> e : primaryKeys.entrySet()) {
            String tableName = e.getKey();
            ImmutableList<String> columnNames = e.getValue();
            if (columnNames.size() > 1) {
                continue;
            }
            pkValuedColumns.add((tableName + "." + columnNames.get(0)).toUpperCase());
        }
        // Only goes one level deep -- doesn't add columns that are foreign key to foreign key to PK, etc.
        for (ForeignKeyDependency fk : foreignKeys) {
            String from = fk.getFromRelation() + "." + fk.getFromColumn(),
                    to = fk.getToRelation() + "." + fk.getToColumn();
            if (pkValuedColumns.contains(to)) {
                pkValuedColumns.add(from);
            }
        }
        this.pkValuedColumns = ImmutableSet.copyOf(pkValuedColumns);
    }

    public ImmutableSet<String> getPkValuedColumns() {
        return pkValuedColumns;
    }

    public boolean hasForeignKeyConstraint(String fromTable, String fromColumn, String toTable, String toColumn) {
        // FIXME(zhangwen): the calls to `toUpperCase` are ugly.
        return foreignKeys.contains(new ForeignKeyDependency(
                fromTable.toUpperCase(), fromColumn.toUpperCase(), toTable.toUpperCase(), toColumn.toUpperCase()
        ));
    }
}
