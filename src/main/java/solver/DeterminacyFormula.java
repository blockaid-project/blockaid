package solver;

import cache.trace.QueryTrace;
import cache.trace.QueryTraceEntry;
import cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Streams;
import com.microsoft.z3.*;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkState;

public abstract class DeterminacyFormula {
    protected final MyZ3Context context;
    protected final Schema schema;
    protected final Instance inst1;
    protected final Instance inst2;

    protected final ImmutableList<BoolExpr> preamble;
    private final String preambleSMT;

    public enum TextOption {
        USE_TEXT,
        NO_TEXT
    }

    protected final TextOption textOption;

    protected DeterminacyFormula(Schema schema, Function<Integer, Instance> makeInstance,
                                 BiFunction<Instance, Instance, List<BoolExpr>> mkPreamble,
                                 TextOption text) {
        this.schema = schema;
        this.context = schema.getContext();
        this.inst1 = makeInstance.apply(0);
        this.inst2 = makeInstance.apply(1);

        // Set prepared expr.
        final long startTime = System.currentTimeMillis();

        this.preamble = ImmutableList.copyOf(mkPreamble.apply(this.inst1, this.inst2));
        this.textOption = text;
        if (text == TextOption.USE_TEXT) {
            Solver solver = schema.getContext().mkRawSolver();
            solver.add(this.preamble.toArray(new BoolExpr[0]));
            String result = solver.toString();
            // Remove the custom sorts from preamble -- we add them back when generating the rest of the formula,
            // because here, sorts that are not used in the preamble but are used later on won't be declared.
            result = result.replaceAll("\\(declare-sort CS![A-Z]+ 0\\)|\\(declare-fun CS![A-Z]+!\\d+ \\(\\) CS![A-Z]+\\)", "");
            // FIXME(zhangwen): this is janky.
            result = result.replaceAll("\\(declare-fun [A-Za-z]+ \\(CS!INT CS!INT\\) Bool\\)", "");

            if (!result.contains("!_NOW")) {
                result += "(declare-fun !_NOW () CS!INT)\n";
            }
            context.mkConst("!_NOW", context.getCustomIntSort());
            this.preambleSMT = result;
        } else {
            this.preambleSMT = null;
        }
//        System.out.println("set prepared expr " + getClass().getName() + ":" + (System.currentTimeMillis() - startTime));
    }

    protected DeterminacyFormula(Schema schema, Function<Integer, Instance> makeInstance,
                                 BiFunction<Instance, Instance, List<BoolExpr>> mkPreamble) {
        this(schema, makeInstance, mkPreamble, TextOption.USE_TEXT);
    }

    protected Iterable<BoolExpr> generateTupleCheck(UnmodifiableLinearQueryTrace queries) {
        List<BoolExpr> exprs = new ArrayList<>();
        for (QueryTraceEntry queryTraceEntry : queries.getAllEntries()) {
            Query query = queryTraceEntry.getQuery().getSolverQuery(schema);
            Relation r1 = query.apply(inst1);
            Relation r2 = query.apply(inst2);
            List<Tuple> tuples = queryTraceEntry.getTuplesStream().map(
                    tuple -> new Tuple(schema, tuple.stream().map(
                            v -> Tuple.getExprFromObject(context, v)
                    ))).collect(Collectors.toList());
            if (!tuples.isEmpty()) {
                Iterables.addAll(exprs, postProcess(r1.doesContainExpr(tuples)));
                Iterables.addAll(exprs, postProcess(r2.doesContainExpr(tuples)));
            }
        }
        return exprs;
    }

    private Iterable<BoolExpr> postProcess(Iterable<BoolExpr> exprs) {
//        for (Expr e : exprs) {
//            if (e.isQuantifier()) {
//                Quantifier q = (Quantifier) e;
//                if (q.isExistential()) {
//                    Expr body = q.getBody();
//                    if (body.isAnd()) {
//                        for (Expr andArg : body.getArgs()) {
//                            if (andArg.isEq()) {
//                                Expr[] eqArgs = andArg.getArgs();
//                                Expr lhs = eqArgs[0], rhs = eqArgs[1];
//                                if (rhs.isVar()) {
//                                    Expr temp = rhs;
//                                    rhs = lhs;
//                                    lhs = temp;
//                                }
//                                System.out.println(lhs + ", " + rhs + ", " + (lhs.equals(rhs)));
//                            }
//                        }
//                    }
//                }
//            }
//        }
//        return Streams.stream(exprs).flatMap(e -> {
//            if (e.isQuantifier()) {
//                Quantifier q = (Quantifier) e;
//                if (q.isExistential()) {
//                    Expr body = q.getBody();
//                    if (body.isAnd()) {
//                        for (Expr andArg : body.getArgs()) {
//                            if (andArg.isEq()) {
//                                Expr[] eqArgs = andArg.getArgs();
//                            }
//                        }
//
//                        return Arrays.stream(body.getArgs()).map(e1 -> (BoolExpr) e1);
//                    }
//                }
//            }
//            return Stream.of(e);
//        }).collect(Collectors.toList());
        return exprs;
    }

    protected Iterable<BoolExpr> generateConstantCheck(UnmodifiableLinearQueryTrace queries) {
        List<BoolExpr> exprs = new ArrayList<>();
        // Constrain constant values.
        for (Map.Entry<String, Object> entry : queries.getConstMap().entrySet()) {
            StringSymbol nameSymbol = context.mkSymbol("!" + entry.getKey());
            Object value = entry.getValue();
            exprs.add(context.mkEq(
                    context.mkConst(nameSymbol, Tuple.getSortFromObject(context, value)),
                    context.mkCustom(entry.getValue())
            ));
        }

        return exprs;
    }

    protected Iterable<BoolExpr> generateNotContains(UnmodifiableLinearQueryTrace queries) {
        /* Both regular and fast unsat share this formula form -- by symmetry, we can write Q(D1) != Q(D2) using
        "not contained in". */
        Query query = queries.getCurrentQuery().getQuery().getSolverQuery(schema);
        Tuple extHeadTup = query.makeFreshHead();
        return List.of(
                query.apply(inst1).doesContainExpr(extHeadTup),
                context.mkNot(query.apply(inst2).doesContainExpr(extHeadTup))
        );
    }

    public Iterable<BoolExpr> makeBodyFormula(UnmodifiableLinearQueryTrace queries) {
        return Iterables.concat(generateTupleCheck(queries), generateConstantCheck(queries),
                generateNotContains(queries));
    }

    protected String makeBodyFormulaSMT(UnmodifiableLinearQueryTrace queries) {
        return Streams.stream(makeBodyFormula(queries))
                .map(formula -> "(assert " + formula + ")")
                .collect(Collectors.joining("\n"));
    }

    public Iterable<BoolExpr> makeCompleteFormula(UnmodifiableLinearQueryTrace queries) {
        return Iterables.concat(preamble, makeBodyFormula(queries));
    }

    public String generateSMT(QueryTrace queries) {
        checkState(textOption == TextOption.USE_TEXT);

        context.startTrackingConsts();
        String bodyFormula = makeBodyFormulaSMT(queries);
        context.stopTrackingConsts();

        StringBuilder sb = new StringBuilder();
        for (Expr constant : context.getConsts()) {
            if (!constant.getSExpr().startsWith("CS!")) {
                sb.append("(declare-fun ").append(constant.getSExpr()).append(" () ").append(constant.getSort().getSExpr()).append(")\n");
            }
        }
        sb.append(bodyFormula);
        String body = sb.toString();

        // only used to generate declarations and assertions for sorts
        String header = context.prepareSortDeclaration();
        return header + this.preambleSMT + body + "(check-sat)";
    }
}
