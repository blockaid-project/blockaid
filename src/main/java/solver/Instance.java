package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public class Instance extends HashMap<String, Relation> {
    final Schema schema;
    final boolean isConcrete;
    private Map<Constraint, Iterable<BoolExpr>> constraints;

    Instance(Schema schema, boolean isConcrete) {
        this.schema = checkNotNull(schema);
        this.isConcrete = isConcrete;
        this.constraints = Collections.emptyMap();
    }

    void setConstraints(Map<Constraint, Iterable<BoolExpr>> constraints) {
        this.constraints = constraints;
    }

    public Map<Constraint, Iterable<BoolExpr>> getConstraints() {
        return constraints;
    }

    public MyZ3Context getContext() {
        return schema.getContext();
    }
}
