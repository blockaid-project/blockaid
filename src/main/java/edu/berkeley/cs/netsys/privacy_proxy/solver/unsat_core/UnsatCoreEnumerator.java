package edu.berkeley.cs.netsys.privacy_proxy.solver.unsat_core;

import com.google.common.collect.ImmutableBiMap;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.MyZ3Context;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class UnsatCoreEnumerator<L> extends AbstractUnsatCoreEnumerator<L> implements AutoCloseable {
    private final MyZ3Context context;
    private final Solver solver;
    private final ImmutableMap<L, BoolExpr> label2BoolConst;
    private final ImmutableMap<BoolExpr, L> boolConst2Label;

    // Sets solver to minimize unsat cores.
    public UnsatCoreEnumerator(MyZ3Context context, Solver solver, Map<L, BoolExpr> labeledExprs, Order order) {
        super(context, labeledExprs.keySet(), order);

        this.context = context;
        this.solver = solver;
        solver.push();

        Params p = context.mkParams();
        p.add("core.minimize", true);
        solver.setParameters(p);

        ImmutableBiMap.Builder<L, BoolExpr> builder = new ImmutableBiMap.Builder<>();
        for (Map.Entry<L, BoolExpr> entry : labeledExprs.entrySet()) {
            L label = entry.getKey();
            BoolExpr boolConst = context.mkBoolConst(label.toString());
            builder.put(label, boolConst);
            solver.add(context.mkImplies(boolConst, entry.getValue()));
        }
        ImmutableBiMap<L, BoolExpr> bm = builder.build();
        this.label2BoolConst = bm;
        this.boolConst2Label = bm.inverse();
    }

    @Override
    protected boolean isUnsatCoreAlwaysMin() {
        return true;
    }

    public Set<L> getStartingUnsatCore() {
        long startMs = System.currentTimeMillis();

//        try {
//            StringBuilder sb = new StringBuilder(solver.toString());
//            int i = 0;
//            for (BoolExpr b : label2BoolConst.values()) {
//                sb.append("(assert (! ").append(b.getSExpr()).append(" :named label").append(i).append("))\n");
//                ++i;
//            }
//            Files.write(Paths.get("/tmp/get_unsat_core_eql.smt2"), sb.toString().getBytes());
//        } catch (IOException e) {
//            throw new RuntimeException(e);
//        }

        // The entire formula had better be unsatisfiable; otherwise there is no unsat core!
        checkArgument(solver.check(label2BoolConst.values().toArray(new BoolExpr[0])) == Status.UNSATISFIABLE,
                "to enumerate unsat cores, the formulas must be unsat");

        long durMs = System.currentTimeMillis() - startMs;
        System.out.println("\t\t| getStartingUnsatCore:\t" + durMs);

        return getUnsatCore().get();
    }

    @Override
    protected Optional<Set<L>> isSubsetSat(Set<L> labels) {
        long startMs = System.currentTimeMillis();
        BoolExpr[] boolConsts = labels.stream().map(label2BoolConst::get).toArray(BoolExpr[]::new);
        Status status = solver.check(boolConsts);

        if (status == Status.SATISFIABLE) {
//            System.out.println("\t\t\t| isSubsetSat:\t" + status + "(" + labels.size() + ")\t" + (System.currentTimeMillis() - startMs));
            return Optional.of(labels);
            // `getModel` is too slow...
//            long modelStartMs = System.currentTimeMillis();
//            Model m = solver.getModel();
//            System.out.println("\t\t\t\t| getModel:\t" + (System.currentTimeMillis() - modelStartMs));
//            // Gather all the labels that are not false in the model.
//            Set<L> satLabels = label2BoolConst.entrySet().stream()
//                    .filter(e -> !m.eval(e.getValue(), false).isFalse())
//                    .map(Map.Entry::getKey)
//                    .collect(Collectors.toSet());
//            checkState(satLabels.containsAll(labels));
//            System.out.println("\t\t\t| isSubsetSat:\t" + status + "(" + labels.size() + " -> " + satLabels.size() + ")\t" + (System.currentTimeMillis() - startMs));
//            return Optional.of(satLabels);
        }
        checkState(status == Status.UNSATISFIABLE, "solver returned: " + status);
//        System.out.println("\t\t\t| isSubsetSat:\t" + status + "\t" + (System.currentTimeMillis() - startMs));
        return Optional.empty();
    }

    @Override
    protected boolean supportsIsSubsetSatWithBound() {
        // Doesn't seem to help.  Disabled for now.
        return true;
    }

    @Override
    protected Optional<Set<L>> isSubsetSat(Set<L> labels, int atLeast) {
        long startMs = System.currentTimeMillis();
        checkArgument(atLeast >= labels.size());
        List<BoolExpr> clauses = labels.stream().map(label2BoolConst::get).collect(Collectors.toList());
        clauses.add(context.mkAtLeast(getLabels().stream().map(label2BoolConst::get).collect(Collectors.toList()),
                atLeast));

        Status status = solver.check(clauses.toArray(new BoolExpr[0]));
        if (status == Status.SATISFIABLE) {
            Model m = solver.getModel();
            // Gather all the labels that are not false in the model.
            Set<L> satLabels = label2BoolConst.entrySet().stream()
                    .filter(e -> !m.eval(e.getValue(), false).isFalse())
                    .map(Map.Entry::getKey)
                    .collect(Collectors.toSet());
            checkState(satLabels.containsAll(labels));
//            System.out.println("\t\t\t| isSubsetSat:\t" + status + "(" + labels.size() + " -> " + satLabels.size() + ")\t" + (System.currentTimeMillis() - startMs));
            return Optional.of(satLabels);
        }
        checkState(status == Status.UNSATISFIABLE, "solver returned: " + status);
//        System.out.println("\t\t\t| isSubsetSat:\t" + status + "\t" + (System.currentTimeMillis() - startMs));
        return Optional.empty();
    }

    @Override
    protected boolean isSubsetSatExists(Set<L> labels, int atLeast) {
        long startMs = System.currentTimeMillis();
        checkArgument(atLeast >= labels.size());
        List<BoolExpr> clauses = labels.stream().map(label2BoolConst::get).collect(Collectors.toList());
        clauses.add(context.mkAtLeast(getLabels().stream().map(label2BoolConst::get).collect(Collectors.toList()),
                atLeast));
        Status status = solver.check(clauses.toArray(new BoolExpr[0]));
//        System.out.println("\t\t\t| isSubsetSatExists (" + atLeast + "):\t" + status + "\t" + (System.currentTimeMillis() - startMs));
        if (status == Status.SATISFIABLE) {
            return true;
        }
        checkState(status == Status.UNSATISFIABLE, "solver returned: " + status);
        return false;
    }

    @Override
    protected Optional<Set<L>> getUnsatCore() {
        return Optional.of(
                Arrays.stream(solver.getUnsatCore()).map(boolConst2Label::get).collect(Collectors.toSet())
        );
    }

    @Override
    public void close() {
        solver.pop();
    }
}
