package edu.berkeley.cs.netsys.privacy_proxy.solver.labels;

import edu.berkeley.cs.netsys.privacy_proxy.solver.Constraint;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Instance;
import edu.berkeley.cs.netsys.privacy_proxy.solver.Query;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkArgument;

public record SubPreamble(Collection<Query> views, Collection<Constraint> constraints) {
    public static SubPreamble fromLabels(Iterable<PreambleLabel> labels) {
        ArrayList<Query> views = new ArrayList<>();
        ArrayList<Constraint> constraints = new ArrayList<>();
        for (PreambleLabel l : labels) {
            switch (l.getKind()) {
                case VIEW -> views.add(((ViewLabel) l).query());
                case CONSTRAINT -> constraints.add(((ConstraintLabel) l).constraint());
                default -> throw new IllegalArgumentException("unrecognized preamble label: " + l);
            }
        }
        return new SubPreamble(views, constraints);
    }

    public static SubPreamble all(Instance inst1, Instance inst2, Collection<Query> views) {
        checkArgument(inst1.getConstraints().keySet().equals(inst2.getConstraints().keySet()));
        return new SubPreamble(views, inst1.getConstraints().keySet());
    }
}
