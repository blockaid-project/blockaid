package planner;

import sql.PrivacyException;

import java.util.Properties;

public interface PrivacyFactory {
    /**
     * Creates a Schema.
     *
     * @param info      Properties hash that contains JsonModel and default schema.
     * @return Created schema
     */
    PrivacyFactoryResult create(Properties info) throws PrivacyException;
}
