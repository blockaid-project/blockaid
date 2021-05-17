package solver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

import java.util.HashMap;

public class Instance extends HashMap<String, Relation> {
    final Schema schema;
    BoolExpr constraint;

    Instance(Schema schema) {
        this(schema, null);
    }

    Instance(Schema schema, BoolExpr constraint) {
        this.schema = schema;
        this.constraint = constraint;
    }

    Context getContext() {
        return schema.getContext();
    }
}
