package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.google.common.collect.*;
import sql.PrivacyQuery;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.google.common.base.Preconditions.checkState;

// Single-use only.
public class CountingBoundEstimator extends BoundEstimator {
    private Schema schema = null;
    private SetMultimap<String, Object> colName2Values = null;

    @Override
    public Map<String, Integer> calculateBounds(Schema schema, QueryTrace trace) {
        // TODO(zhangwen): this is ugly.
        checkState(this.colName2Values == null,
                "a CountingBoundEstimator object can only `calculateBounds` once");

        HashMultimap<String, Object> colName2Values = HashMultimap.create();
        for (QueryTraceEntry e : trace.getAllEntries()) {
            if (!e.hasTuples()) {
                continue;
            }
            List<List<Object>> tuples = e.getTuples();
            int numColumns = tuples.get(0).size();

            PrivacyQuery q = e.getQuery();
            List<Set<String>> normColNames = IntStream.range(0, numColumns)
                    .mapToObj(q::getNormalizedProjectColumnsByIdx)
                    .collect(Collectors.toList());

            for (List<Object> tup : e.getTuples()) {
                for (int colIdx = 0; colIdx < tup.size(); ++colIdx) {
                    Set<String> colNames = normColNames.get(colIdx);
                    if (colNames.size() > 1) {
                        continue;
                    }
                    colName2Values.put(
                            Iterables.getOnlyElement(colNames),
                            tup.get(colIdx)
                    );
                }
            }
        }

        HashMap<String, Integer> bounds = new HashMap<>();
        for (String relationName : schema.getRelationNames()) {
            bounds.put(relationName, 0);
        }

        for (String colName : colName2Values.keySet()) {
            String relationName = colName.split("\\.")[0];
            int currBound = bounds.get(relationName);
            int newBound = colName2Values.get(colName).size();
            if (newBound > currBound) {
                bounds.put(relationName, newBound);
            }
        }

        this.schema = schema;
        this.colName2Values = colName2Values;
        return bounds;
    }

    public ImmutableSetMultimap<String, Object> getPkValues() {
        checkState(this.schema != null);
        checkState(this.colName2Values != null);

        ImmutableSetMultimap.Builder<String, Object> builder = new ImmutableSetMultimap.Builder<>();
        for (String relationName : schema.getRelationNames()) {
            ImmutableList<String> pkColumnNames = schema.getRawSchema().getPrimaryKeyColumns(relationName);
            if (pkColumnNames == null || pkColumnNames.size() != 1) {
                // Only supported if the table has exactly one primary-key column.
                continue;
            }
            String quantifiedPkColumnName = relationName + "." + pkColumnNames.get(0);
            builder.putAll(relationName, colName2Values.get(quantifiedPkColumnName));
        }

        ImmutableSetMultimap<String, Object> res = builder.build();
        System.out.println(res);
        return res;
    }
}
