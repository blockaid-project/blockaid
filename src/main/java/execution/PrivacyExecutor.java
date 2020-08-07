package execution;

import sql.ParserResult;

public interface PrivacyExecutor {
    Object execute(ParserResult result) throws Exception;
}
