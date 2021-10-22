package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.*;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.MyZ3Context;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.Label;

import java.util.*;
import java.util.stream.Collectors;

public class FindMinimalSat implements AutoCloseable {
    private final MyZ3Context context;
    private final Solver solver;

    public FindMinimalSat(MyZ3Context context, Solver solver) {
        this.context = context;
        this.solver = solver;
        solver.push();
    }

    public static Set<Expr> gatherConstants(Expr e) {
        HashSet<Expr> constraints = new HashSet<>();
        gatherConstants(e, constraints);
        return constraints;
    }

    public static <T extends Expr> Set<Expr> gatherConstants(Iterable<T> exprs) {
        HashSet<Expr> constraints = new HashSet<>();
        for (Expr e : exprs) {
            gatherConstants(e, constraints);
        }
        return constraints;
    }

    private static <T extends Expr> void gatherConstants(Iterable<T> exprs, Set<Expr> constants) {
        for (Expr e : exprs) {
            gatherConstants(e, constants);
        }
    }

    private static void gatherConstants(Expr e, Set<Expr> constants) {
        if (e.isConst()) {
            constants.add(e);
            return;
        }
        if (e.isApp()) { // Other kinds of application.
            for (Expr arg : e.getArgs()) {
                gatherConstants(arg, constants);
            }
            return;
        }
        if (e.isQuantifier()) {
            Quantifier q = (Quantifier) e;
            gatherConstants(q.getBody(), constants);
            return;
        }
        if (e.isVar()) { // Bound variable.
            return;
        }
        throw new IllegalArgumentException("unsupported expression: " + e);
    }

    public Set<Label> compute(UnsatCoreFormulaBuilder.Formulas<Label> fs) {
        ImmutableList<BoolExpr> bg = fs.getBackground();
        ImmutableMap<Label, BoolExpr> labeledExprs = fs.getLabeledExprs();

        HashSet<Expr> allConsts = new HashSet<>();
        gatherConstants(bg, allConsts);
        gatherConstants(labeledExprs.values(), allConsts);

        HashMap<BoolExpr, Label> boolConst2Label = new HashMap<>();
        ArrayList<BoolExpr> antecedent = new ArrayList<>();
        int i = 0;
        for (Map.Entry<Label, BoolExpr> entry : labeledExprs.entrySet()) {
            BoolExpr boolConst = context.mkBoolConst("L" + i);
            boolConst2Label.put(boolConst, entry.getKey());
            antecedent.add(context.mkImplies(boolConst, entry.getValue()));
            ++i;
        }

        solver.add(context.myMkForall(
                allConsts,
                context.mkImplies(
                        context.mkAnd(antecedent),
                        context.mkAnd(bg)
                )
                ));

        HashSet<BoolExpr> coreInverse = new HashSet<>();
        for (BoolExpr b : boolConst2Label.keySet()) {
            if (coreInverse.contains(b)) {
                continue;
            }

            coreInverse.add(b);
            System.out.println("Checking " + coreInverse.size() + "...");

            Status res = solver.check(coreInverse.stream().map(context::mkNot).toArray(BoolExpr[]::new));
            switch (res) {
                case SATISFIABLE -> {
                    coreInverse.clear();
                    Model model = solver.getModel();
                    for (BoolExpr b0 : boolConst2Label.keySet()) {
                        if (!model.eval(b0, false).isTrue()) {
                            coreInverse.add(b0);
                        }
                    }
                }
                case UNSATISFIABLE -> coreInverse.remove(b);
                default -> throw new RuntimeException("solver returned: " + res);
            }
        }

        // Yet to explore: [low..high)
//        while (low < high) {
//            int mid = (low + high) / 2;
//            System.out.println("Checking: " + mid + "...");
//
//            solver.push();
//            solver.add(context.mkAtMost(boolConst2Label.keySet(), mid));
//            try {
//                String path = "/tmp/find_minimal_sat.smt2";
//                Files.write(Paths.get(path), solver.toString().getBytes());
//            } catch (IOException e) {
//                throw new RuntimeException(e);
//            }
//            Status res = solver.check();
////            Status res = solver.check(context.mkAtMost(boolConst2Label.keySet(), mid));
//
//            switch (res) {
//                case SATISFIABLE -> {
//                    Model model = solver.getModel();
//                    core = new ArrayList<>();
//                    for (BoolExpr b : boolConst2Label.keySet()) {
//                        if (model.eval(b, false).isTrue()) {
//                            core.add(b);
//                        }
//                    }
//                    high = core.size();
//                }
//                case UNSATISFIABLE -> low = mid + 1;
//                default -> throw new RuntimeException("solver returned: " + res);
//            }
//
//            solver.pop();
//        }

        HashSet<BoolExpr> core = new HashSet<>(boolConst2Label.keySet());
        core.removeAll(coreInverse);
        return core.stream().map(boolConst2Label::get).collect(Collectors.toSet());
    }

    @Override
    public void close() {
        solver.pop();
    }
}
