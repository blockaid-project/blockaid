package server;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonProperty;

/**
 * POJO for server specific configurations.
 */
@JsonIgnoreProperties(ignoreUnknown = true)
public class ServerConfig {
    public final int port;

    @JsonCreator
    public ServerConfig(@JsonProperty("port") int port) {
        this.port = port;
    }
}