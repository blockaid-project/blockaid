package edu.berkeley.cs.netsys.privacy_proxy.solver.context;

import com.google.common.collect.Iterables;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

import java.util.Collection;
import java.util.stream.Collectors;

public class MergedTrackedDecls implements TrackedDecls {
    private final Iterable<Expr<?>> consts;
    private final Iterable<FuncDecl<?>> funcDecls;

    <T extends TrackedDecls> MergedTrackedDecls(Collection<T> trackedDecls) {
        this.consts = Iterables.concat(
                trackedDecls.stream().map(TrackedDecls::getConsts).collect(Collectors.toList())
        );
        this.funcDecls = Iterables.concat(
                trackedDecls.stream().map(TrackedDecls::getFuncDecls).collect(Collectors.toList())
        );
    }

    @Override
    public Iterable<Expr<?>> getConsts() {
        return consts;
    }

    @Override
    public Iterable<FuncDecl<?>> getFuncDecls() {
        return funcDecls;
    }
}
