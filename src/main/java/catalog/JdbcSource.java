package catalog;

import java.util.Map;

/**
 * An extension of {@link DataSource}
 * that is constructed from database.
 */
public class JdbcSource extends DataSource {
    private String username;
    private String password;

    public JdbcSource(long id,
                      String type,
                      String name,
                      String datasourceType,
                      String url,
                      long dsSetId,
                      String username,
                      String password) {
        super(id, type, name, datasourceType, url, dsSetId);
        this.username = username;
        this.password = password;
    }

    public String getUsername() {
        return username;
    }

    public void setUsername(String username) {
        this.username = username;
    }

    public String getPassword() {
        return password;
    }

    public void setPassword(String password) {
        this.password = password;
    }

    public Map<String, Object> getProperties(Map<String, Object> prop) {
        prop.put("username", this.username);
        prop.put("password", this.password);
        prop.put("factory", "com.qubole.quark.plugins.jdbc.JdbcFactory");

        return prop;
    }

    @Override
    public String[] values() {
        return new String[]{String.valueOf(this.getId()),
                this.getType(),
                this.getUrl(),
                this.getName(),
                String.valueOf(this.getDsSetId()),
                this.getDatasourceType(),
                null,
                null,
                this.username,
                this.password};
    }
}
