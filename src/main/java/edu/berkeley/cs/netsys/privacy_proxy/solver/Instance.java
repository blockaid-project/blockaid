package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.BoolSort;
import com.microsoft.z3.FuncDecl;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.HashMap;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public class Instance<C extends Z3ContextWrapper<?, ?, ?, ?>> {
    private final String name;
    private final Schema<C> schema;
    final boolean isConcrete;
    // TODO(zhangwen): make these immutable.
    private final Map<String, Relation<C>> name2Rel;
    private final Map<FuncDecl<BoolSort>, String> funcDecl2RelName;

    Instance(String name, Schema<C> schema, boolean isConcrete) {
        this.name = name;
        this.schema = checkNotNull(schema);
        this.isConcrete = isConcrete;
        this.name2Rel = new HashMap<>();
        this.funcDecl2RelName = new HashMap<>();
    }

    public void put(String relName, Relation<C> rel) {
        if (rel instanceof GeneralRelation genRel) {
            RelationFunction f = genRel.getFunction();
            if (f instanceof Z3Function z3f) {
                funcDecl2RelName.put(z3f.getFunctionDecl(), relName);
            }
        }
        name2Rel.put(relName, rel);
    }

    public Relation<C> get(String relName) {
        return name2Rel.get(relName);
    }

    String getRelNameFromFuncDecl(FuncDecl<BoolSort> fd) {
        return funcDecl2RelName.get(fd);
    }

    public Schema<C> getSchema() {
        return schema;
    }

    public String getName() {
        return name;
    }

    public C getContext() {
        return schema.getContext();
    }
}
