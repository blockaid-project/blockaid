package server;

import org.apache.calcite.avatica.Meta;
import org.apache.calcite.avatica.jdbc.JdbcMeta;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;

import com.fasterxml.jackson.databind.ObjectMapper;

import java.io.File;
import java.io.IOException;
import java.sql.SQLException;
import java.util.Arrays;
import java.util.List;
import java.util.Properties;

/**
 * Bridge between Privacy Checker and Avatica.
 */
public class PrivacyMetaFactoryImpl implements Meta.Factory {
    protected static final Log LOG = LogFactory.getLog(Main.class);
    public static ServerConfig serverConfig;

    // invoked via reflection
    public PrivacyMetaFactoryImpl() {
        super();
    }

    @Override
    public Meta create(List<String> args) {
        String url = "jdbc:quark:fat:db:";

        try {
            if (args.size() == 1) {
                String filePath = args.get(0);
                ObjectMapper objectMapper = new ObjectMapper();
                serverConfig = objectMapper.readValue(new File(filePath), ServerConfig.class);

                url = url + filePath;
            } else {
                throw new RuntimeException(
                        "1 argument expected. Received " + Arrays.toString(args.toArray()));
            }
            return new JdbcMeta(url, new Properties());
        } catch (SQLException | IOException e) {
            throw new RuntimeException(e);
        }
    }
}