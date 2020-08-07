package fatjdbc;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonProperty;

/**
 * Created by adeshr on 3/2/16.
 */
@JsonIgnoreProperties(ignoreUnknown = true)
public class CatalogDetail {
    public final DbCredentials dbCredentials;

    @JsonCreator
    public CatalogDetail(@JsonProperty("dbCredentials") DbCredentials dbCredentials) {
        this.dbCredentials = dbCredentials;
    }

    /**
     * Store database credentials
     */
    public static class DbCredentials {
        public final String url;
        public final String username;
        public final String password;
        public final String encryptionKey;
        public final String encrypt;

        @JsonCreator
        DbCredentials(@JsonProperty("url") String url,
                      @JsonProperty("username") String username,
                      @JsonProperty("password") String password,
                      @JsonProperty("encrypt_key") String encrpytionKey,
                      @JsonProperty("encrypt") String encrypt) {
            this.url = url;
            this.username = username;
            this.password = password;
            this.encryptionKey = encrpytionKey;
            this.encrypt = encrypt;
        }
    }
}