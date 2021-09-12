package solver.labels;

import java.util.Collection;

public interface Label {
    Kind getKind();
    Collection<Operand> getOperands();

    enum Kind {
        EQUALITY,
        LESS_THAN,
        RETURNED_ROW,
    }
}
