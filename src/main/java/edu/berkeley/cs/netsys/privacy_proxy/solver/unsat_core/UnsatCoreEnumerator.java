package edu.berkeley.cs.netsys.privacy_proxy.solver.unsat_core;

import com.google.common.collect.ImmutableBiMap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.LabeledBoolExpr;
import edu.berkeley.cs.netsys.privacy_proxy.solver.UnsatCoreFormulaBuilder;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.util.LogLevel;
import org.checkerframework.checker.nullness.qual.Nullable;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Logger.printMessage;

public class UnsatCoreEnumerator<L, BL, C extends Z3ContextWrapper<?, ?, ?, ?>> extends AbstractUnsatCoreEnumerator<L, C> implements AutoCloseable {
    private final C context;
    private final Solver solver;
    private final ImmutableMap<BoolExpr, BL> boolConst2bgLabel;
    private final ImmutableBiMap<L, BoolExpr> label2BoolConst;

    public enum Option {
        SOLVER_MINIMIZE_CORE
    }

    private final ImmutableSet<Option> options;

    private @Nullable BoolExpr[] solverCore;

    // Sets solver to minimize unsat cores.
    public UnsatCoreEnumerator(C context, Solver solver, UnsatCoreFormulaBuilder.Formulas<L, BL> fs, Order order,
                               Set<Option> options) {
        super(context, fs.labeledExprs().keySet(), order);

        this.context = context;
        this.solver = solver;
        solver.push();

        this.options = Sets.immutableEnumSet(options);
        if (options.contains(Option.SOLVER_MINIMIZE_CORE)) {
            Params p = context.mkParams();
            p.add("core.minimize", true);
            solver.setParameters(p);
        }

        {
            ImmutableMap.Builder<BoolExpr, BL> builder = ImmutableMap.builder();
            for (LabeledBoolExpr<BL> bgExpr : fs.background()) {
                BL label = bgExpr.label();
                if (label == null) {
                    solver.add(bgExpr.expr());
                } else {
                    BoolExpr boolConst = context.mkBoolConst(label.toString());
                    solver.assertAndTrack(bgExpr.expr(), boolConst);
                    builder.put(boolConst, label);
                }
            }
            this.boolConst2bgLabel = builder.build();
        }

        {
            ImmutableBiMap.Builder<L, BoolExpr> builder = new ImmutableBiMap.Builder<>();
            for (Map.Entry<L, BoolExpr> entry : fs.labeledExprs().entrySet()) {
                L label = entry.getKey();
                BoolExpr boolConst = context.mkBoolConst(label.toString());
                builder.put(label, boolConst);
                solver.add(context.mkImplies(boolConst, entry.getValue()));
            }
            this.label2BoolConst = builder.build();
        }
    }

    @Override
    protected boolean isUnsatCoreAlwaysMin() {
        return options.contains(Option.SOLVER_MINIMIZE_CORE);
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
        solverCore = null;
        checkArgument(solver.check(label2BoolConst.values().toArray(new BoolExpr[0])) == Status.UNSATISFIABLE,
                "to enumerate unsat cores, the formulas must be unsat");
        Set<L> core = getUnsatCore().get();

        long durMs = System.currentTimeMillis() - startMs;
        System.out.println("\t\t| getStartingUnsatCore:\t" + durMs);

        return core;
    }

    @Override
    protected Optional<Set<L>> isSubsetSat(Set<L> labels) {
        long startNs = System.nanoTime();
        BoolExpr[] boolConsts = labels.stream().map(label2BoolConst::get).toArray(BoolExpr[]::new);
        solverCore = null;
        Status status = solver.check(boolConsts);
        printMessage("\t\t\t| isSubsetSat:\t" + status + "\t" + (System.nanoTime() - startNs) / 1000000, LogLevel.VERBOSE);

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

        solverCore = null;
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
        solverCore = null;
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
        long startNs = System.nanoTime();
        solverCore = solver.getUnsatCore();
        printMessage("\t\t| getUnsatCore:\t" + (System.nanoTime() - startNs) / 1000000, LogLevel.VERBOSE);
        return Optional.of(
                Arrays.stream(solverCore)
                        .map(b -> label2BoolConst.inverse().get(b))
                        .filter(Objects::nonNull)
                        .collect(Collectors.toSet())
        );
    }

    // Must call `getUnsatCore()` first.
    public Set<BL> getUnsatCorePreamble() {
        checkState(solverCore != null, "must call getUnsatCore before calling this method");
        return Arrays.stream(solverCore)
                .map(boolConst2bgLabel::get)
                .filter(Objects::nonNull)
                .collect(Collectors.toSet());
    }

    @Override
    public void close() {
        solver.pop();
    }
}
