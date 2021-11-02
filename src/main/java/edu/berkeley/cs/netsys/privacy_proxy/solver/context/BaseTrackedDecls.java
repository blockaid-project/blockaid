package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public class BaseTrackedDecls implements TrackedDecls {
    private final Set<Expr<?>> consts;
    private final Set<FuncDecl<?>> funcDecls;

    BaseTrackedDecls() {
        this.consts = new HashSet<>();
        this.funcDecls = new HashSet<>();
    }

    boolean containsConst(Expr<?> c) {
        return consts.contains(c);
    }

    boolean containsFuncDecl(FuncDecl<?> f) {
        return funcDecls.contains(f);
    }

    void addConst(Expr<?> c) {
        consts.add(c);
    }

    void addFuncDecl(FuncDecl<?> f) {
        funcDecls.add(f);
    }

    public Iterable<Expr<?>> getConsts() {
        return Collections.unmodifiableSet(consts);
    }

    public Iterable<FuncDecl<?>> getFuncDecls() {
        return Collections.unmodifiableSet(funcDecls);
    }
}
