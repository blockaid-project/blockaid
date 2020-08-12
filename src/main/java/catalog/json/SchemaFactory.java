package catalog.json;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.common.collect.ImmutableList;

import planner.MetadataSchema;
import sql.PrivacyException;
import planner.DataSourceSchema;
import planner.PrivacyFactory;
import planner.PrivacyFactoryResult;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.List;
import java.util.Properties;

/**
 * Sets up and organizes the planner with tables from all federated data sources.
 * The info argument encodes all the required information (described below) as
 * JSON.
 * Consider an example where there are 3 data sources:
 * <ul>
 * <li>CANONICAL</li>
 * <li>CUBES</li>
 * <li>VIEWS</li>
 * </ul>
 * CANONICAL is the default. Each of the data sources have many schemas and
 * tables. This class and its dependents set up such that the tables can be
 * referred as follows:
 * <ul>
 * <li><i>canonical.default.lineitem</i> refers to a table in DEFAULT in CANONICAL.</li>
 * <li><i>canonical.tpch.customers</i> refers to a table in TPCH in CANONICAL.</li>
 * <li><i>lineitem</i> refers to a table in DEFAULT in CANONICAL.</li>
 * <li><i>CUBES.PUBLIC.WEB_RETURNS</i> refers to a table in PUBLIC in CUBES.</li>
 * </ul>
 *
 */
public class SchemaFactory implements PrivacyFactory {
    private static final Logger LOG = LoggerFactory.getLogger(SchemaFactory.class);

    /**
     * Creates list of QuarkSchema
     *
     * @param info A JSON string which represents a RootSchema and its dependent objects.
     * @return
     * @throws PrivacyException
     */
    public PrivacyFactoryResult create(Properties info) throws PrivacyException {
        try {
            ObjectMapper objectMapper = new ObjectMapper();
            RootSchema rootSchema = objectMapper.readValue((String) info.get("model"), RootSchema.class);

            ImmutableList.Builder<DataSourceSchema> schemaList = new ImmutableList.Builder<>();

            for (catalog.json.DataSourceSchema secondary : rootSchema.dataSources) {
                schemaList.add(secondary);
            }

            List<DataSourceSchema> schemas = schemaList.build();

            return new PrivacyFactoryResult(schemas, null,
                    rootSchema.defaultDataSource != null ? schemas.get(rootSchema.defaultDataSource)
                            : null
            );
        } catch (java.io.IOException e) {
            LOG.error("Unexpected Exception during create", e);
            throw new PrivacyException(e);
        }
    }
}
