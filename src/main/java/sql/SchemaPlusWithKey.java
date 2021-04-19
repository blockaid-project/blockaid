package sql;

import org.apache.calcite.schema.SchemaPlus;

import java.util.List;
import java.util.Map;

public class SchemaPlusWithKey {
    public SchemaPlus schema;
    public Map<String, List<String>> primaryKeys;

    public SchemaPlusWithKey(SchemaPlus schema, Map<String, List<String>> primaryKeys) {
        this.schema = schema;
        this.primaryKeys = primaryKeys;
    }
}
