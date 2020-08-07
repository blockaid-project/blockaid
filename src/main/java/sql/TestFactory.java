package sql;

import planner.PrivacySchema;

import java.util.List;
import java.util.Properties;

/**
 * Created by rajatv on 11/12/15.
 */
public abstract class TestFactory {
    private final PrivacySchema defaultSchema;

    protected TestFactory(PrivacySchema defaultSchema) {
        this.defaultSchema = defaultSchema;
    }
    public abstract List<PrivacySchema> create(Properties info) throws PrivacyException;

    public PrivacySchema getDefaultSchema() {
        return defaultSchema;
    }
}
