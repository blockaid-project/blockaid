package cache.labels;

public interface Label {
    Kind getKind();

    enum Kind {
        EQUALITY,
        RETURNED_ROW,
    }
}
