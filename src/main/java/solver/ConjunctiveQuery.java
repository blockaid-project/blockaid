package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;

import java.util.List;

// TODO
public class ConjunctiveQuery extends PSJ {
    public ConjunctiveQuery(Schema schema, List<String> relations) {
        super(schema, relations);
    }

    @Override
    protected BoolExpr predicateGenerator(Context context, Tuple... tuples) {
        return super.predicateGenerator(context, tuples);
    }

    @Override
    protected Tuple headSelector(Tuple... tuples) {
        return new Tuple();
    }

    @Override
    protected Sort[] headTypeSelector(Sort[]... types) {
        return new Sort[0];
    }
}
