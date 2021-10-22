package edu.berkeley.cs.netsys.privacy_proxy.sql.preprocess;

import edu.berkeley.cs.netsys.privacy_proxy.sql.ParserResult;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;
import edu.berkeley.cs.netsys.privacy_proxy.sql.SchemaPlusWithKey;

import java.util.List;
import java.util.Optional;

public interface Preprocessor {
    Optional<PrivacyQuery> perform(ParserResult result, SchemaPlusWithKey schema, List<Object> parameters,
                                   List<String> paramNames);
}
