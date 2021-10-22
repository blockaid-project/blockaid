package edu.berkeley.cs.netsys.privacy_proxy.solver;

import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Streams;
import com.microsoft.z3.BoolExpr;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.ConstraintLabel;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.PreambleLabel;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.ReturnedRowLabel;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.ViewLabel;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;

public class RRLUnsatCoreDeterminacyFormula {
    private final DeterminacyFormula baseFormula;
    private final ImmutableList<Constraint> constraints;
    private final ImmutableList<Policy> policies;
    private final ImmutableList<Query> views;

    private static final Pattern RR_PATTERN = Pattern.compile("ReturnedRowLabel!(\\d+)!(\\d+)");
    private static final Pattern PREAMBLE_PATTERN = Pattern.compile("(Constraint|View)!(\\d+)");

    public RRLUnsatCoreDeterminacyFormula(Schema schema, ImmutableList<Policy> policies) {
        Instance inst1 = schema.makeFreshInstance("instance0"),
                inst2 = schema.makeFreshInstance("instance1");

        Z3ContextWrapper context = schema.getContext();
        ArrayList<NamedBoolExpr> preamble = new ArrayList<>();

        Map<Constraint, Iterable<BoolExpr>> c1 = inst1.getConstraints(), c2 = inst2.getConstraints();
        checkArgument(c1.keySet().equals(c2.keySet()));
        this.constraints = ImmutableList.copyOf(c1.keySet());
        for (int i = 0; i < constraints.size(); ++i) {
            Constraint c = constraints.get(i);
            preamble.add(new NamedBoolExpr(
                    context.mkAnd(Iterables.concat(c1.get(c), c2.get(c))),
                    "Constraint!" + i
            ));
        }

        this.policies = policies;
        this.views = schema.getPolicyQueries(policies);
        for (int i = 0; i < views.size(); ++i) {
            Query v = views.get(i);
            preamble.add(new NamedBoolExpr(
                    context.mkAnd(v.apply(inst1).isContainedInExpr(v.apply(inst2))),
                    "View!" + i
            ));
        }

        String preambleSMT = DeterminacyFormula.makePreambleSMTNamed(preamble);
        ImmutableList<BoolExpr> rawPreamble = preamble.stream().map(NamedBoolExpr::expr)
                .collect(ImmutableList.toImmutableList());

        this.baseFormula = new DeterminacyFormula(schema, inst1, inst2, rawPreamble, TextOption.USE_TEXT, preambleSMT);
    }

    private List<NamedBoolExpr> generateTupleCheckNamed(UnmodifiableLinearQueryTrace trace) {
        Schema schema = baseFormula.schema;
        Z3ContextWrapper context = baseFormula.context;
        ArrayList<NamedBoolExpr> exprs = new ArrayList<>();

        List<QueryTraceEntry> allEntries = trace.getAllEntries();
        for (int queryIdx = 0; queryIdx < allEntries.size(); ++queryIdx) {
            QueryTraceEntry qte = allEntries.get(queryIdx);
            if (!qte.hasTuples()) {
                continue;
            }
            Query query = qte.getQuery().getSolverQuery(schema);
            Relation r1 = query.apply(baseFormula.inst1);
            List<Tuple> tuples = DeterminacyFormula.getTupleObjects(qte, schema);

            for (int rowIdx = 0; rowIdx < tuples.size(); ++rowIdx) {
                Tuple tuple = tuples.get(rowIdx);
                ReturnedRowLabel l = new ReturnedRowLabel(queryIdx, rowIdx);
                exprs.add(new NamedBoolExpr(context.mkAnd(r1.doesContainExpr(tuple)), l.toString()));
            }
        }

        return exprs;
    }

    public String generateUnsatCoreSMT(UnmodifiableLinearQueryTrace trace) {
        return baseFormula.generateSMTFromString(() -> {
            Stream<NamedBoolExpr> formulas = Streams.concat(
                    generateTupleCheckNamed(trace).stream(),
                    Streams.stream(baseFormula.generateConstantCheck(trace)).map(NamedBoolExpr::makeUnnamed),
                    Streams.stream(baseFormula.generateNotContains(trace)).map(NamedBoolExpr::makeUnnamed)
            );
            return formulas.map(NamedBoolExpr::makeAssertion).collect(Collectors.joining("\n"));
        }, "(set-option :produce-unsat-cores true)\n", "(get-unsat-core)\n(exit)");
    }

    public Set<ReturnedRowLabel> extractRRLabels(Collection<String> core) {
        Set<ReturnedRowLabel> res = new HashSet<>();
        for (String label : core) {
            Matcher m = RR_PATTERN.matcher(label);
            if (!m.matches()) {
                continue;
            }
            res.add(new ReturnedRowLabel(Integer.parseInt(m.group(1)), Integer.parseInt(m.group(2))));
        }
        return res;
    }

    public Set<PreambleLabel> extractPreambleLabels(Collection<String> core) {
        Set<PreambleLabel> res = new HashSet<>();
        for (String label : core) {
            Matcher m = PREAMBLE_PATTERN.matcher(label);
            if (!m.matches()) {
                continue;
            }

            int i = Integer.parseInt(m.group(2));
            res.add(switch (m.group(1)) {
                case "Constraint" -> new ConstraintLabel(constraints.get(i));
                case "View" -> new ViewLabel(policies.get(i));
                default -> throw new IllegalArgumentException("parse preamble label failed: " + m.group(0));
            });
        }
        return res;
    }
}
