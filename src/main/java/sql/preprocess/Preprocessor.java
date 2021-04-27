package sql.preprocess;

import sql.ParserResult;
import sql.PrivacyQuery;
import sql.SchemaPlusWithKey;

import java.util.List;
import java.util.Optional;

public interface Preprocessor {
    Optional<PrivacyQuery> perform(ParserResult result, SchemaPlusWithKey schema, Object[] parameters,
                                   List<String> paramNames);
}
