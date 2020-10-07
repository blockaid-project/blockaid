package sql;

import java.sql.SQLException;

/**
 * Created by amoghm on 3/4/16.
 */
public interface Parser {
    ParserResult parse(String sql) throws SQLException;
}
