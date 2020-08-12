package catalog.json;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;

import java.util.Arrays;
import java.util.List;

/**
 * Describes the root element in the JSON template.
 */
public class RootSchema {
    public final List<String> supportedVersions = Arrays.asList("2.0");
    public final List<DataSourceSchema> dataSources;
    public final Integer defaultDataSource;
    public final RelSchema relSchema;

    @JsonCreator
    public RootSchema(@JsonProperty("version") String version,
                      @JsonProperty("dataSources") List<DataSourceSchema> dataSources,
                      @JsonProperty("defaultDataSource") Integer defaultDataSource,
                      @JsonProperty("relSchema") RelSchema relSchema) {
        if (version == null) {
            throw new RuntimeException("version is required");
        }

        if (!supportedVersions.contains(version)) {
            throw new RuntimeException("Unsupported Version: '" + version + "'");
        }

        if (dataSources != null && !dataSources.isEmpty() && defaultDataSource == null) {
            throw new RuntimeException("Default DataSource must be specified");
        }
        this.dataSources = dataSources;
        this.defaultDataSource = defaultDataSource;
        this.relSchema = relSchema;
    }
}
