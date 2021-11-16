package edu.berkeley.cs.netsys.privacy_proxy.sql;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeField;
import org.apache.calcite.rel.type.RelDataTypeSystem;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.schema.Table;
import org.apache.calcite.sql.type.SqlTypeFactoryImpl;
import edu.berkeley.cs.netsys.privacy_proxy.solver.ForeignKeyDependency;
import org.apache.calcite.sql.type.SqlTypeName;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class SchemaPlusWithKey {
    // FIXME(zhangwen): put all constraints in the schema?
    public final SchemaPlus schema;
    private final ImmutableMap<String, ImmutableList<String>> primaryKeys;
    private final ImmutableSet<ForeignKeyDependency> foreignKeys;

    private final ImmutableSet<String> fkColumns;
    // Every column that stores values of a primary key type (e.g., a PK column, or a foreign key to a PK column).
    private final ImmutableSet<String> pkValuedColumns;

    private static final SqlTypeFactoryImpl SQL_TYPE_FACTORY = new SqlTypeFactoryImpl(RelDataTypeSystem.DEFAULT);
    private final Map<String, RelDataType> table2Type;

    private final ImmutableMap<String, SqlTypeName> constName2Type;

    public SchemaPlusWithKey(SchemaPlus schema,
                             ImmutableMap<String, ImmutableList<String>> primaryKeys,
                             ImmutableSet<ForeignKeyDependency> foreignKeys,
                             ImmutableMap<String, SqlTypeName> constName2Type) {
        this.schema = checkNotNull(schema);
        this.primaryKeys = checkNotNull(primaryKeys);
        this.foreignKeys = checkNotNull(foreignKeys);
        this.table2Type = new HashMap<>();
        this.constName2Type = constName2Type;

        HashSet<String> pkValuedColumns = new HashSet<>();
        ImmutableSet.Builder<String> fkColsBuilder = new ImmutableSet.Builder<>();
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
            String from = fk.fromRelation() + "." + fk.fromColumn(),
                    to = fk.toRelation() + "." + fk.toColumn();
            if (pkValuedColumns.contains(to)) {
                pkValuedColumns.add(from);
                fkColsBuilder.add(from);
            }
        }
        this.fkColumns = fkColsBuilder.build();
        this.pkValuedColumns = ImmutableSet.copyOf(pkValuedColumns);
    }

    // Returns empty if the relation has no primary key.
    public Optional<ImmutableList<String>> getPrimaryKeyColumns(String relationName) {
        return Optional.ofNullable(primaryKeys.get(relationName.toUpperCase()));
    }

    public ImmutableSet<String> getPkValuedColumns() {
        return pkValuedColumns;
    }

    public ImmutableSet<String> getFkColumns() {
        return fkColumns;
    }

    public boolean hasForeignKeyConstraint(String fromTable, String fromColumn, String toTable, String toColumn) {
        // FIXME(zhangwen): the calls to `toUpperCase` are ugly.
        return foreignKeys.contains(new ForeignKeyDependency(
                fromTable.toUpperCase(), fromColumn.toUpperCase(), toTable.toUpperCase(), toColumn.toUpperCase()
        ));
    }

    public RelDataType getTypeForTable(String tableName) {
        // FIXME(zhangwen): maybe fix the upper- and lower-case.
        return table2Type.computeIfAbsent(tableName.toLowerCase(), t -> {
            Table table = Objects.requireNonNull(schema.getTable(t));
            return table.getRowType(SQL_TYPE_FACTORY);
        });
    }

    public List<String> getRelationNames() {
        return schema.getTableNames().stream().map(String::toUpperCase).collect(Collectors.toList());
    }

    public Stream<String> getColumnNames(String tableName) {
        return getTypeForTable(tableName).getFieldList().stream().map(RelDataTypeField::getName);
    }

    public SqlTypeName getTypeForConst(String constName) {
        if (constName.equals("_NOW")) {
            return SqlTypeName.TIMESTAMP;
        }
        SqlTypeName typeName = constName2Type.get(constName);
        checkArgument(typeName != null, "unrecognized constant: " + constName);
        return typeName;
    }
}
