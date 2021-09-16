package solver.labels;

public interface PreambleLabel {
    enum Kind {
        CONSTRAINT,
        VIEW;
    }

    Kind getKind();
}
