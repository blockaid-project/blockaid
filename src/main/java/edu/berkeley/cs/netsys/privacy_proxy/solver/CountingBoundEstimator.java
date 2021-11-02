package edu.berkeley.cs.netsys.privacy_proxy.solver;

import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.sql.PrivacyQuery;
import edu.berkeley.cs.netsys.privacy_proxy.sql.SchemaPlusWithKey;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.google.common.base.Preconditions.checkState;

// Single-use only.
public class CountingBoundEstimator<C extends Z3ContextWrapper<?, ?, ?, ?>> extends BoundEstimator<C> {
    private SchemaPlusWithKey rawSchema = null;
    private SetMultimap<String, Object> colName2Values = null;

    @Override
    public Map<String, Integer> calculateBounds(Schema<C> schema, UnmodifiableLinearQueryTrace trace) {
        // TODO(zhangwen): this is ugly.
        checkState(this.colName2Values == null,
                "a CountingBoundEstimator object can only `calculateBounds` once");
        this.rawSchema = schema.getRawSchema();

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
        for (String relationName : rawSchema.getRelationNames()) {
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

        this.colName2Values = colName2Values;
        return bounds;
    }

    public ImmutableSetMultimap<String, Object> getPkValues() {
        checkState(this.rawSchema != null);
        checkState(this.colName2Values != null);

        ImmutableSetMultimap.Builder<String, Object> builder = new ImmutableSetMultimap.Builder<>();
        for (String relationName : rawSchema.getRelationNames()) {
            Optional<ImmutableList<String>> oPkColumnNames = rawSchema.getPrimaryKeyColumns(relationName);
            if (oPkColumnNames.isEmpty()) {
                continue;
            }

            ImmutableList<String> pkColumnNames = oPkColumnNames.get();
            if (pkColumnNames.size() != 1) {
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
