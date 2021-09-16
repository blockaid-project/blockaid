package solver.labels;

import solver.Query;

public record ViewLabel(Query query) implements PreambleLabel {
    @Override
    public Kind getKind() {
        return Kind.VIEW;
    }
}
