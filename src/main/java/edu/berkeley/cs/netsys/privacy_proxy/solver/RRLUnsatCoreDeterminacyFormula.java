package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.*;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.QueryTraceEntry;
import edu.berkeley.cs.netsys.privacy_proxy.cache.trace.UnmodifiableLinearQueryTrace;
import com.microsoft.z3.BoolExpr;
import edu.berkeley.cs.netsys.privacy_proxy.policy_checker.Policy;
import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;
import edu.berkeley.cs.netsys.privacy_proxy.solver.labels.*;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.PRUNE_PREAMBLE;

public class RRLUnsatCoreDeterminacyFormula<C extends Z3ContextWrapper<?, ?, ?, ?>> {
    private final DeterminacyFormula<C, Instance<C>> baseFormula;
    private final PreambleLabelCollection preambleLabels;

    private static final Pattern RR_PATTERN = Pattern.compile("ReturnedRowLabel_(\\d+)_(\\d+)_\\d+");

    public RRLUnsatCoreDeterminacyFormula(Schema<C> schema, ImmutableList<Policy> policies) {
        Instance<C> inst1 = schema.makeUnboundedInstance("instance0"),
                inst2 = schema.makeUnboundedInstance("instance1");

        this.preambleLabels = new PreambleLabelCollection(schema.getDependencies(), policies);

        // Use linked hash map to preserve insertion order -- easy for debugging.
        LinkedHashMap<PreambleLabel, NamedBoolExpr> preamble = new LinkedHashMap<>();
        preambleLabels.forEachWithName((name, label) -> {
            Iterable<BoolExpr> formulas = switch (label.getKind()) {
                case POLICY -> {
                    Query<C> v = ((PolicyLabel) label).policy().getSolverQuery(schema);
                    yield v.apply(inst1).isContainedInExpr(v.apply(inst2));
                }
                case DEPENDENCY -> {
                    Dependency d = ((DependencyLabel) label).dependency();
                    yield Iterables.concat(d.apply(inst1), d.apply(inst2));
                }
            };

            NamedBoolExpr expr = switch (PRUNE_PREAMBLE) {
                case UNSAT_CORE -> new NamedBoolExpr(formulas, name);
                case OFF, COARSE -> NamedBoolExpr.makeUnnamed(formulas);
            };
            preamble.put(label, expr);
        });

        ImmutableMap<PreambleLabel, String> preambleSMT = DeterminacyFormula.makePreambleSMTNamed(preamble);
        ImmutableMap<PreambleLabel, ImmutableList<BoolExpr>> rawPreamble = ImmutableMap.copyOf(
                Maps.transformValues(preamble, LabeledBoolExpr::exprs)
        );
        this.baseFormula = new DeterminacyFormula<>(schema, inst1, inst2, rawPreamble, TextOption.USE_TEXT, preambleSMT);
    }

    private List<NamedBoolExpr> generateTupleCheckNamed(UnmodifiableLinearQueryTrace trace) {
        Schema<C> schema = baseFormula.schema;
        ArrayList<NamedBoolExpr> exprs = new ArrayList<>();

        List<QueryTraceEntry> allEntries = trace.getAllEntries();
        for (int queryIdx = 0; queryIdx < allEntries.size(); ++queryIdx) {
            QueryTraceEntry qte = allEntries.get(queryIdx);
            if (!qte.hasTuples()) {
                continue;
            }
            Query<C> query = qte.getQuery().getSolverQuery(schema);
            Relation<C> r1 = query.apply(baseFormula.inst1);
            List<Tuple<C>> tuples = DeterminacyFormula.getTupleObjects(qte, schema);

            for (int rowIdx = 0; rowIdx < tuples.size(); ++rowIdx) {
                Tuple<C> tuple = tuples.get(rowIdx);
                ReturnedRowLabel l = new ReturnedRowLabel(queryIdx, rowIdx);
                exprs.add(new NamedBoolExpr(r1.doesContainExpr(tuple), l.toString()));
            }
        }

        return exprs;
    }

    public String generateUnsatCoreSMT(UnmodifiableLinearQueryTrace trace) {
        Stream<NamedBoolExpr> formulas = Streams.concat(
                generateTupleCheckNamed(trace).stream(),
                Streams.stream(baseFormula.generateConstantCheck(trace)).map(NamedBoolExpr::makeUnnamed),
                Streams.stream(baseFormula.generateNotContains(trace)).map(NamedBoolExpr::makeUnnamed)
        );
        String bodySMT = formulas.map(NamedBoolExpr::makeAssertion).collect(Collectors.joining("\n"));

        return baseFormula.generateSMTFromString(bodySMT,
                "(set-option :produce-unsat-cores true)\n",
                "(get-unsat-core)\n(exit)",
                baseFormula.computeRelevantPreambleLabels(trace));
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
        return core.stream()
                .flatMap(name -> preambleLabels.parse(name).stream())
                .collect(Collectors.toSet());
    }
}
