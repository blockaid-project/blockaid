package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Sort;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.List;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;

public class UnionQuery<C extends Z3ContextWrapper<?, ?, ?, ?>> extends Query<C> {
    public final ImmutableList<Query<C>> queries;
    private final List<Sort> headTypes;

    public UnionQuery(List<Query<C>> queries) {
        super();

        Query<C> firstQuery = Iterables.getFirst(queries, null);
        checkArgument(firstQuery != null, "union must take at least one query");
        for (Query<C> query : queries) {
            checkArgument(query.getSchema() == firstQuery.getSchema());
        }

        this.queries = ImmutableList.copyOf(queries);
        this.headTypes = firstQuery.headTypes();
    }

    @Override
    public Schema<C> getSchema() {
        return queries.get(0).getSchema();
    }

    @Override
    public List<Sort> headTypes() {
        return headTypes;
    }

    @Override
    public Iterable<BoolExpr> doesContain(Instance<C> instance, Tuple<C> tuple) {
        C context = instance.getContext();
        BoolExpr[] exprs = new BoolExpr[queries.size()];
        for (int i = 0; i < queries.size(); ++i) {
            exprs[i] = context.mkAnd(queries.get(i).doesContain(instance, tuple));
        }
        return List.of(context.mkOr(exprs));
    }

    @Override
    public List<Tuple<C>> generateTuples(Instance<C> instance) {
        return queries.stream().map(q -> q.generateTuples(instance)).flatMap(List::stream).collect(Collectors.toList());
    }

    @Override
    public List<BoolExpr> generateExists(Instance<C> instance) {
        return queries.stream().map(q -> q.generateExists(instance)).flatMap(List::stream).collect(Collectors.toList());
    }
}
