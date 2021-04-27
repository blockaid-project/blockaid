package sql;

import org.apache.calcite.schema.SchemaPlus;

import java.util.*;

public class SchemaPlusWithKey {
    public SchemaPlus schema;
    public Map<String, List<String>> primaryKeys;
    private final Set<List<String>> foreignKeys;

    /**
     * Takes "ownership" of arguments.
     */
    public SchemaPlusWithKey(SchemaPlus schema, Map<String, List<String>> primaryKeys, Set<List<String>> foreignKeys) {
        this.schema = schema;
        this.primaryKeys = Collections.unmodifiableMap(primaryKeys);
        this.foreignKeys = Collections.unmodifiableSet(foreignKeys);
    }

    public boolean hasForeignKeyConstraint(String fromTable, String fromColumn, String toTable, String toColumn) {
        return foreignKeys.contains(Arrays.asList(
                fromTable.toUpperCase(), fromColumn.toUpperCase(), toTable.toUpperCase(), toColumn.toUpperCase()
        ));
    }
}
