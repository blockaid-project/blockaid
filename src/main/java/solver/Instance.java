package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public class Instance extends HashMap<String, Relation> {
    final Schema schema;
    List<BoolExpr> constraints;
    final boolean isConcrete;

    Instance(Schema schema, boolean isConcrete) {
        this.schema = checkNotNull(schema);
        this.isConcrete = isConcrete;
        this.constraints = Collections.emptyList();
    }

    public Context getContext() {
        return schema.getContext();
    }
}
