package sql.preprocess;

import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.SqlOrderBy;
import org.apache.calcite.sql.SqlSelect;
import sql.ParserResult;
import sql.PrivacyQuery;
import sql.PrivacyQueryFactory;
import sql.SchemaPlusWithKey;
import util.SqlNodes;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Strips order by, fetch next, offset.
 */
public class StripOrderBy implements Preprocessor {
    public static final StripOrderBy INSTANCE = new StripOrderBy();

    private StripOrderBy() {}

    public Optional<PrivacyQuery> perform(ParserResult result, SchemaPlusWithKey schema, List<Object> parameters,
                                          List<String> paramNames) {
        boolean changed = false;

        SqlNode node = result.getSqlNode();
        if (node.getKind() == SqlKind.ORDER_BY) {
            node = ((SqlOrderBy) node).query;
            changed = true;
        }
        if (node.getKind() == SqlKind.SELECT) {
            SqlSelect select = (SqlSelect) node;
            if (select.getOrderList() != null || select.getFetch() != null || select.getOffset() != null) {
                SqlSelect newSelect = SqlNodes.shallowCopy(select);
                newSelect.setOrderBy(null);
                newSelect.setFetch(null);
                newSelect.setOffset(null);
                node = newSelect;
                changed = true;
            }
        }

        if (!changed) {
            return Optional.empty();
        }

        ShiftDynParams.Result res = ShiftDynParams.perform(node, parameters, paramNames);
        ParserResult newPR = new ParserResult(res.node());
        return Optional.of(PrivacyQueryFactory.createPrivacyQuery(newPR, schema, res.params(), res.paramNames()));
    }
}
