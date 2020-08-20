package planner;

import java.util.List;


public class PrivacyView {
    public final String name;
    public final String viewSql;
    public final String table;
    public final List<String> schema;
    public final List<String> alias;

    public PrivacyView(String name, String viewSql, String table, List<String> schema,
                     List<String> alias) {
        this.name = name;
        this.viewSql = viewSql;
        this.table = table;
        this.schema = schema;
        this.alias = alias;
    }
}