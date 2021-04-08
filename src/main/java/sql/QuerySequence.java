package sql;

import java.util.ArrayList;

public class QuerySequence extends ArrayList<QueryWithResult> {
    public QuerySequence copy() {
        QuerySequence querySequence = new QuerySequence();
        for (QueryWithResult q : this) {
            querySequence.add(q.copy());
        }
        return querySequence;
    }
}
