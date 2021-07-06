package solver;

import java.util.List;

public interface Dependency extends Constraint {
    List<String> getFromRelations();
    List<String> getToRelations();
}
