package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

import java.util.HashMap;

import static com.google.common.base.Preconditions.checkNotNull;

public class Instance extends HashMap<String, Relation> {
    final Schema schema;
    BoolExpr constraint;
    final boolean isConcrete;

    Instance(Schema schema, boolean isConcrete) {
        this(schema, isConcrete, null);
    }

    Instance(Schema schema, boolean isConcrete, BoolExpr constraint) {
        this.schema = checkNotNull(schema);
        this.isConcrete = isConcrete;
        this.constraint = constraint;
    }

    Context getContext() {
        return schema.getContext();
    }
}
