package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import static com.google.common.base.Preconditions.*;

// TODO(zhangwen): separate class for unbounded instances?
public class Instance<C extends Z3ContextWrapper<?, ?, ?, ?>> {
    private final String name;
    private final Schema<C> schema;
    private final boolean isBounded;
    private final ImmutableMap<String, Relation<C>> name2Rel;
    private final ImmutableMap<FuncDecl<BoolSort>, String> funcDecl2RelName;

    Instance(String name, Schema<C> schema, boolean isBounded, ImmutableMap<String, Relation<C>> name2Rel,
             ImmutableMap<FuncDecl<BoolSort>, String> funcDecl2RelName) {
        if (isBounded) {
            checkArgument(name2Rel.values().stream().allMatch(r -> r instanceof ConcreteRelation<C>));
        }

        this.name = name;
        this.schema = checkNotNull(schema);
        this.isBounded = isBounded;
        this.name2Rel = checkNotNull(name2Rel);
        this.funcDecl2RelName = funcDecl2RelName;
    }

    public boolean isBounded() {
        return isBounded;
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

    static class Builder<C extends Z3ContextWrapper<?, ?, ?, ?>> {
        private final String name;
        private final Schema<C> schema;
        private final ImmutableMap.Builder<String, Relation<C>> name2RelBuilder;
        private final ImmutableMap.Builder<FuncDecl<BoolSort>, String> funcDecl2RelNameBuilder;

        /**
         * Variables that constitute the contents of a BOUNDED instance (including "exists" variables).
         * TODO(zhangwen): adding vars explicitly is error-prone; extract from isntance directly?
         * TODO(zhangwen): have a separate bounded builder?
         */
        private final ImmutableList.Builder<Expr<?>> dbVarsBuilder;

        Builder(String name, Schema<C> schema) {
            this.name = name;
            this.schema = schema;
            this.name2RelBuilder = new ImmutableMap.Builder<>();
            this.funcDecl2RelNameBuilder = new ImmutableMap.Builder<>();
            this.dbVarsBuilder = new ImmutableList.Builder<>();
        }

        public void put(String relName, Relation<C> rel) {
            if (rel instanceof GeneralRelation genRel) {
                RelationFunction f = genRel.getFunction();
                if (f instanceof Z3Function z3f) {
                    funcDecl2RelNameBuilder.put(z3f.functionDecl(), relName);
                }
            }
            name2RelBuilder.put(relName, rel);
        }

        public void addDbVar(Expr<?> variable) {
            dbVarsBuilder.add(variable);
        }

        public Instance<C> buildUnbounded() {
            ImmutableList<Expr<?>> dbVars = dbVarsBuilder.build();
            checkState(dbVars.isEmpty(), "unbounded formula shouldn't have dbVars");
            return new Instance<>(name, schema, false, name2RelBuilder.build(), funcDecl2RelNameBuilder.build());
        }

        public BoundedInstance<C> buildBounded() {
            return new BoundedInstance<>(name, schema, name2RelBuilder.build(), funcDecl2RelNameBuilder.build(), dbVarsBuilder.build());
        }
    }
}
