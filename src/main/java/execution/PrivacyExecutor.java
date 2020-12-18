package execution;

import sql.ParserResult;
import sql.PrivacyException;

import java.sql.PreparedStatement;
import java.sql.SQLException;

public interface PrivacyExecutor {
    Object execute(ParserResult result) throws Exception;

    PreparedStatement prepare(ParserResult result) throws Exception;
}
