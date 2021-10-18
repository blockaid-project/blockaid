package sql.preprocess;

import org.apache.calcite.sql.SqlBasicCall;
import org.apache.calcite.sql.SqlIdentifier;
import org.apache.calcite.sql.SqlNode;

import java.util.Optional;

class Util {
    static Optional<String> getTableName(SqlNode node) {
        return switch (node.getKind()) {
            case IDENTIFIER -> {
                SqlIdentifier id = (SqlIdentifier) node;
                if (id.names.size() <= 2) {
                    yield Optional.of(id.names.get(id.names.size() - 1));
                }
                yield Optional.empty();
            }
            case AS -> {
                SqlBasicCall call = (SqlBasicCall) node;
                SqlIdentifier aliasNode = call.operand(1);
                if (!aliasNode.isSimple()) {
                    yield Optional.empty();
                }
                String alias = aliasNode.getSimple();

                Optional<String> lhsTableName = getTableName(call.operand(0));
                if (lhsTableName.isEmpty() || !lhsTableName.get().equals(alias)) {
                    yield Optional.empty();
                }
                yield lhsTableName;
            }
            default -> Optional.empty();
        };
    }
}
