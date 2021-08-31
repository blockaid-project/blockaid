package cache.unsat_core;

import cache.BoundedUnsatCoreDeterminacyFormula;
import cache.MyUnsatCoreDeterminacyFormula;
import cache.labels.Label;
import cache.labels.ReturnedRowLabel;
import cache.trace.*;
import com.google.common.collect.*;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import policy_checker.Policy;
import solver.*;
import solver.executor.CVC4Executor;
import solver.executor.ProcessSMTExecutor;
import solver.executor.SMTExecutor;
import solver.executor.VampireProofExecutor;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static util.TerminalColor.*;

public class ReturnedRowUnsatCoreEnumerator extends AbstractUnsatCoreEnumerator<ReturnedRowLabel> {
    private final Schema schema;
    private final Collection<Query> views;
    private final QueryTrace trace;
    private final String smtPreamble;
    private Set<ReturnedRowLabel> prevCore = null;

    public static AbstractUnsatCoreEnumerator<ReturnedRowLabel> create(Schema schema, Collection<Policy> policies,
                                                        Collection<Query> views, QueryTrace trace) {
        int maxBound = Collections.max(new CountingBoundEstimator().calculateBounds(schema, trace).values());
        // FIXME(zhangwen): this is a hack for small traces.
        if (maxBound <= 10) {
            MyZ3Context context = schema.getContext();
            Solver solver = context.mkSolver();
            BoundedUnsatCoreDeterminacyFormula formula = BoundedUnsatCoreDeterminacyFormula.create(schema, policies,
                    views, trace, BoundedUnsatCoreDeterminacyFormula.LabelOption.RETURNED_ROWS_ONLY);
            solver.add(Iterables.toArray(formula.makeBackgroundFormulas(), BoolExpr.class));
            for (Map.Entry<Label, BoolExpr> e : formula.makeLabeledExprs().entrySet()) {
                solver.add(context.mkImplies(context.mkBoolConst(e.getKey().toString()), e.getValue()));
            }
            return new UnsatCoreEnumerator<>(context, solver,
                    formula.makeLabeledExprs().entrySet().stream()
                            .collect(Collectors.toMap(e -> (ReturnedRowLabel) e.getKey(), Map.Entry::getValue)),
                    Order.ARBITRARY);
        }

        // TODO(zhangwen): This code is duplicated.
        ArrayList<ReturnedRowLabel> rrls = new ArrayList<>();
        int queryIdx = 0;
        for (QueryTraceEntry entry : trace.getAllEntries()) {
            for (int tupIdx = 0; tupIdx < entry.getTuples().size(); ++tupIdx) {
                rrls.add(new ReturnedRowLabel(queryIdx, tupIdx));
            }
            ++queryIdx;
        }
        return new ReturnedRowUnsatCoreEnumerator(schema, views, trace, rrls);
    }

    private ReturnedRowUnsatCoreEnumerator(Schema schema, Collection<Query> views,
                                           QueryTrace trace, Collection<ReturnedRowLabel> labels) {
        super(schema.getContext(), labels, Order.DECREASING);
        this.schema = schema;
        this.views = views;
        this.trace = trace;

        MyZ3Context context = schema.getContext();
        {
            Solver solver = context.mkSolver();
            MyUnsatCoreDeterminacyFormula myFormula = new MyUnsatCoreDeterminacyFormula(schema, views, trace);
            solver.add(Iterables.toArray(myFormula.makeBackgroundFormulas(), BoolExpr.class));
            Map<ReturnedRowLabel, BoolExpr> labeledExprs = myFormula.makeLabeledExprs();
            for (Map.Entry<ReturnedRowLabel, BoolExpr> entry : labeledExprs.entrySet()) {
                if (labels.contains(entry.getKey())) {
                    solver.add(context.mkImplies(
                            context.mkBoolConst(entry.getKey().toString()),
                            entry.getValue()
                    ));
                }
            }
            this.smtPreamble = solver.toString();
        }
    }

    private Status solveNormal(Set<ReturnedRowLabel> labels) {
        ArrayList<ProcessSMTExecutor> executors = new ArrayList<>();
        CountDownLatch latch = new CountDownLatch(1);

        StringBuilder smtBuilder = new StringBuilder(smtPreamble);
        for (ReturnedRowLabel l : labels) {
            smtBuilder.append("(assert ").append(l).append(")\n");
        }
        String smtVampire = smtBuilder.toString();
//        executors.add(new VampireProofExecutor("vampire_lrs", smtVampire, latch, "lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_10"));
        executors.add(new VampireProofExecutor("vampire_dis", smtVampire, latch, "dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_10"));
        executors.add(new VampireProofExecutor("vampire_lrs1011", smtVampire, latch, "lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:sos=theory:sp=occurrence:urr=ec_only:updr=off_10"));

//        smtBuilder = new StringBuilder("(set-option :produce-unsat-cores true)\n");
//        smtBuilder.append(smtPreamble);
//        for (ReturnedRowLabel l : labels) {
//            smtBuilder.append("(assert (! ").append(l).append(" :named !").append(l).append("))\n");
//        }
//        smtBuilder.append("(check-sat)");
//        smtBuilder.append("(get-unsat-core)");
//        try {
//            Files.write(Paths.get("/tmp/get_unsat_core_cvc4.smt2"), smtBuilder.toString().getBytes());
//        } catch (IOException e) {
//            throw new RuntimeException(e);
//        }
//        executors.add(new CVC4Executor("cvc4", smtBuilder.toString(), latch, true, true, false));

        for (SMTExecutor executor : executors) {
            executor.start();
        }

        long startMs = System.currentTimeMillis();
        try {
            latch.await(2000, TimeUnit.MILLISECONDS);
            for (SMTExecutor executor : executors) {
                executor.signalShutdown();
            }
            for (SMTExecutor executor : executors) {
                executor.join();
            }
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        long durMs = System.currentTimeMillis() - startMs;

        Set<ReturnedRowLabel> smallestCore = null;
        for (ProcessSMTExecutor e : executors) {
            switch (e.getResult()) {
                case SATISFIABLE:
                    return Status.SATISFIABLE;
                case UNKNOWN:
                    continue;
            }

            System.out.println(e.getName());
            Set<ReturnedRowLabel> core = Pattern.compile("ReturnedRowLabel!(\\d+)!(\\d+)").matcher(e.getOutput())
                    .results()
                    .map(r -> new ReturnedRowLabel(Integer.parseInt(r.group(1)), Integer.parseInt(r.group(2))))
                    .collect(Collectors.toSet());
            core.retainAll(labels);
            System.out.println(ANSI_RED + ANSI_BLUE_BACKGROUND + core + ANSI_RESET);
            if (smallestCore == null || smallestCore.size() > core.size()) {
                smallestCore = core;
            }
        }

        if (durMs > 500) {
            try {
                Files.write(Paths.get("/tmp/get_unsat_core_vampire.smt2"), smtVampire.getBytes());
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }

        if (smallestCore == null) {
            return Status.UNKNOWN;
        }

        this.prevCore = smallestCore;
        return Status.UNSATISFIABLE;

//        VampireCASCProofExecutor executor = new VampireCASCProofExecutor("vampire", smt, null);
//        String output = executor.doRunRaw();
//        if (output.contains("Termination reason: Satisfiable\n")) {
//            return Status.SATISFIABLE;
//        }
//
//        if (output.contains("Termination reason: Refutation\n")) {
//            // TODO(zhangwen): this is ugly.
//            Set<ReturnedRowLabel> core = Pattern.compile("ReturnedRowLabel!(\\d+)!(\\d+)").matcher(output).results()
//                    .map(r -> new ReturnedRowLabel(Integer.parseInt(r.group(1)), Integer.parseInt(r.group(2))))
//                    .collect(Collectors.toSet());
//            System.out.println(ANSI_RED + ANSI_BLUE_BACKGROUND + core + ANSI_RESET);
//
//            this.prevCore = core;
//            return Status.UNSATISFIABLE;
//        }
//
//        try {
//            Files.write(Paths.get("/tmp/get_unsat_core.smt2"), smt.getBytes());
//        } catch (IOException e) {
//            throw new RuntimeException(e);
//        }
//
//        return Status.UNKNOWN;
    }

    @Override
    protected Optional<Set<ReturnedRowLabel>> getUnsatCore() {
        return Optional.ofNullable(this.prevCore);
    }

    @Override
    protected Optional<Set<ReturnedRowLabel>> isSubsetSat(Set<ReturnedRowLabel> labels) {
        this.prevCore = null;
        if (labels.size() > 3) {
            long startMs = System.currentTimeMillis();
            Status res = solveNormal(labels);
            System.out.println("\t\t| Normal:\t" + (System.currentTimeMillis() - startMs));
            switch (res) {
                case SATISFIABLE:
                    return Optional.of(labels);
                case UNSATISFIABLE:
                    return Optional.empty();
            }
        }

        SubQueryTrace sqt = trace.getSubTrace(
                labels.stream()
                        .map(rrl -> new QueryTupleIdxPair(rrl.getQueryIdx(), rrl.getRowIdx()))
                        .collect(ImmutableList.toImmutableList())
        );

        BoundEstimator boundEstimator = new UnsatCoreBoundEstimator(new CountingBoundEstimator());
        Map<String, Integer> bounds = boundEstimator.calculateBounds(schema, sqt);
        Map<String, Integer> slackBounds = Maps.transformValues(bounds, n -> n + 2);

        BoundedDeterminacyFormula formula = new BoundedDeterminacyFormula(schema, views, slackBounds, true,
                DeterminacyFormula.TextOption.NO_TEXT, sqt.computeKnownRows(schema));
        Solver solver = schema.getContext().mkSolver();
        solver.add(Iterables.toArray(formula.makeCompleteFormula(sqt), BoolExpr.class));
        Status status = solver.check();
        if (status == Status.SATISFIABLE) {
            return Optional.of(labels);
        }
        checkState(status == Status.UNSATISFIABLE, "solver returned: " + status);
        System.out.println(ANSI_RED + labels.size() + "\t" + labels + ANSI_RESET);
        return Optional.empty();
    }

    @Override
    public void close() {}
}
