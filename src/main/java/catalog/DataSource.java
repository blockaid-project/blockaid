package catalog;

import java.sql.SQLException;
import java.util.HashMap;
import java.util.Map;

public class DataSource {
    private long id;
    private String type;
    private String url;
    private String name;
    private String datasourceType;
    private long dsSetId;

    public DataSource(long id,
                      String type,
                      String name,
                      String datasourceType,
                      String url,
                      long dsSetId) {
        this.id = id;
        this.type = type;
        this.name = name;
        this.datasourceType = datasourceType;
        this.url = url;
        this.dsSetId = dsSetId;
    }

    public long getId() {
        return id;
    }

    public void setId(long id) {
        this.id = id;
    }

    public String getType() {
        return type;
    }

    public void setType(String type) {
        this.type = type;
    }

    public String getUrl() {
        return url;
    }

    public void setUrl(String url) {
        this.url = url;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getDatasourceType() {
        return datasourceType;
    }

    public void setDatasourceType(String datasourceType) {
        this.datasourceType = datasourceType;
    }

    public long getDsSetId() {
        return dsSetId;
    }

    public void setDsSetId(long dsSetId) {
        this.dsSetId = dsSetId;
    }

    public Map<String, Object> getProperties(long defaultDataSourceId) {
        Map<String, Object> properties = new HashMap<>();
        properties.put("type", this.getType());
        properties.put("url", this.getUrl());
        properties.put("name", this.getName());

        if (this.datasourceType.equals("JDBC")) {
            properties = ((JdbcSource) this).getProperties(properties);
        }

        if (defaultDataSourceId == this.id) {
            properties.put("default", "true");
        } else {
            properties.put("default", "false");
        }

        return properties;
    }

    public String[] values() throws SQLException {
        throw new SQLException("Method not implemented for " + this.getClass());
    }
}
