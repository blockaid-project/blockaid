package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.FuncDecl;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.MyZ3Context;

import java.util.HashMap;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public class Instance {
    private final String name;
    final Schema schema;
    final boolean isConcrete;
    private final Map<String, Relation> name2Rel;
    private ImmutableMap<Constraint, Iterable<BoolExpr>> constraints;
    private final Map<FuncDecl, String> funcDecl2RelName;

    Instance(String name, Schema schema, boolean isConcrete) {
        this.name = name;
        this.schema = checkNotNull(schema);
        this.isConcrete = isConcrete;
        this.name2Rel = new HashMap<>();
        this.constraints = ImmutableMap.of();
        this.funcDecl2RelName = new HashMap<>();
    }

    public void put(String relName, Relation rel) {
        if (rel instanceof GeneralRelation genRel) {
            RelationFunction f = genRel.getFunction();
            if (f instanceof Z3Function z3f) {
                funcDecl2RelName.put(z3f.getFunctionDecl(), relName);
            }
        }
        name2Rel.put(relName, rel);
    }

    public Relation get(String relName) {
        return name2Rel.get(relName);
    }

    String getRelNameFromFuncDecl(FuncDecl fd) {
        return funcDecl2RelName.get(fd);
    }

    public String getName() {
        return name;
    }

    void setConstraints(Map<Constraint, Iterable<BoolExpr>> constraints) {
        this.constraints = ImmutableMap.copyOf(constraints);
    }

    public Map<Constraint, Iterable<BoolExpr>> getConstraints() {
        return constraints;
    }

    public MyZ3Context getContext() {
        return schema.getContext();
    }
}
