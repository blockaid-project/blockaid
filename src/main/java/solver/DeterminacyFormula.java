package solver;

import cache.QueryTrace;
import cache.QueryTraceEntry;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Streams;
import com.microsoft.z3.*;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;

public abstract class DeterminacyFormula {
    protected final MyZ3Context context;
    protected final Schema schema;
    protected final Instance inst1;
    protected final Instance inst2;

    protected final ImmutableList<BoolExpr> preamble;
    private final String preambleSMT;

    protected enum TextOption {
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

    protected Iterable<BoolExpr> generateTupleCheck(QueryTrace queries) {
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
                exprs.add(r1.doesContainExpr(tuples));
                exprs.add(r2.doesContainExpr(tuples));
            }
        }
        return exprs;
    }

    protected Iterable<BoolExpr> generateConstantCheck(QueryTrace queries) {
        List<BoolExpr> exprs = new ArrayList<>();
        // Constrain constant values.
        for (Map.Entry<String, Integer> entry : queries.getConstMap().entrySet()) {
            StringSymbol nameSymbol = context.mkSymbol("!" + entry.getKey());
            exprs.add(context.mkEq(
                    context.mkConst(nameSymbol, context.getCustomIntSort()),
                    context.mkCustomInt(entry.getValue())
            ));
        }

        return exprs;
    }

    public Iterable<BoolExpr> makeBodyFormula(QueryTrace queries) {
        /* Both regular and fast unsat share this formula form -- by symmetry, we can write Q(D1) != Q(D2) using
        "not contained in". */
        Query query = queries.getCurrentQuery().getQuery().getSolverQuery(schema);
        Tuple extHeadTup = query.makeFreshHead();
        List<BoolExpr> notContainsFormulas = List.of(
                query.doesContain(inst1, extHeadTup),
                context.mkNot(query.doesContain(inst2, extHeadTup)));
        return Iterables.concat(generateTupleCheck(queries), generateConstantCheck(queries), notContainsFormulas);
    }

    protected String makeBodyFormulaSMT(QueryTrace queries) {
        return Streams.stream(makeBodyFormula(queries))
                .map(formula -> "(assert " + formula + ")")
                .collect(Collectors.joining("\n"));
    }

    public Iterable<BoolExpr> makeCompleteFormula(QueryTrace queries) {
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
