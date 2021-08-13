package plugin.jdbc;

import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.schema.Table;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import planner.PrivacySchema;
import sql.QueryContext;

import planner.PrivacyColumn;
import planner.PrivacyTable;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Map;

/**
 * Created by rvenkatesh on 7/10/17.
 */
public class JdbcSchema extends PrivacySchema {
    private static final Logger LOG = LoggerFactory.getLogger(JdbcSchema.class);
    private final ImmutableMap<String, Table> tableMap;

    public JdbcSchema(String name, ResultSet resultSet, boolean isCaseSensitive,
                      ImmutableMap<String, Integer> dataTypes) throws SQLException {
        super(isCaseSensitive ? name : name.toUpperCase());

        ImmutableMap.Builder<String, Table> tableBuilder = new ImmutableMap.Builder<>();
        while (!resultSet.isAfterLast() && resultSet.getString(1).equals(name)) {
            ImmutableList.Builder<PrivacyColumn> columnBuilder = new ImmutableList.Builder<>();
            String currentTable = resultSet.getString(2);
            boolean skip = resultSet.getString(1).equals("information_schema") || resultSet.getString(1).equals("mysql") || resultSet.getString(1).equals("performance_schema")|| resultSet.getString(1).equals("sys");
            while (resultSet.getString(2).equals(currentTable)) {
                if (!skip) {
                    String columnName = resultSet.getString(3);
                    if (!isCaseSensitive) {
                        columnName = columnName.toUpperCase();
                    }
                    String typeName = resultSet.getString(4).toUpperCase();
                    Integer dataType = null;
                    if (typeName.equals("JSON")) {
                        // HACK(zhangwen): JDBC doesn't seem to return the JSON type, so we handle it specially.
                        dataType = dataTypes.get("TEXT");
                    } else {
                        for (String key : dataTypes.keySet()) {
                            if (typeName.matches(key)) {
                                dataType = dataTypes.get(key);
                                break;
                            }
                        }
                    }

                    if (dataType == null) {
                        throw new SQLException("DataType `" + resultSet.getString(4) + "` is not supported");
                    }

                    columnBuilder.add(new PrivacyColumn(columnName, dataType));
                    LOG.debug("Adding column:  " + resultSet.getString(1) + " : "
                            + resultSet.getString(2) + " : "
                            + resultSet.getString(3) + " : "
                            + resultSet.getString(4));
                }
                if (!resultSet.next()) {
                    break;
                }
            }

            if (!skip) {
                if (!isCaseSensitive) {
                    currentTable = currentTable.toUpperCase();
                }
                tableBuilder.put(currentTable, new PrivacyTable(this, currentTable, columnBuilder.build()));
            }
        }

        tableMap = tableBuilder.build();
    }

    @Override
    public void initialize(QueryContext queryContext, SchemaPlus schemaPlus) {
        this.schemaPlus = schemaPlus;
        for (Map.Entry<String, Table> entry : tableMap.entrySet()) {
            this.schemaPlus.add(entry.getKey(), entry.getValue());
        }
    }

    @Override
    public Map<String, Table> getTableMap() {
        return tableMap;
    }
}