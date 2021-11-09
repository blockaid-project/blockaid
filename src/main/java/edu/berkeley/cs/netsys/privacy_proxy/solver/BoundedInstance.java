package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

public class BoundedInstance<C extends Z3ContextWrapper<?, ?, ?, ?>> extends Instance<C> {
    private final ImmutableList<Expr<?>> dbVars;

    BoundedInstance(Schema<C> schema, ImmutableMap<String, Relation<C>> name2Rel,
                    ImmutableMap<FuncDecl<BoolSort>, String> funcDecl2RelName, ImmutableList<Expr<?>> dbVars) {
        super(schema, true, name2Rel, funcDecl2RelName);
        this.dbVars = dbVars;
    }

    /**
     * Gets all the variables that constitute the contents of tables of this instance, including "exists" variables.
     * @return all variables.
     */
    public ImmutableList<Expr<?>> getAllVars() {
        return dbVars;
    }
}
