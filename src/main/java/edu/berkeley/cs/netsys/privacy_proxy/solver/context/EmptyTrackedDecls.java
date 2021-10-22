package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

import java.util.Collections;

public class EmptyTrackedDecls implements TrackedDecls {
    private static final EmptyTrackedDecls INSTANCE = new EmptyTrackedDecls();

    private EmptyTrackedDecls() {}

    public static EmptyTrackedDecls getSingleton() {
        return INSTANCE;
    }

    @Override
    public Iterable<Expr> getConsts() {
        return Collections.emptyList();
    }

    @Override
    public Iterable<FuncDecl> getFuncDecls() {
        return Collections.emptyList();
    }
}
