package solver;

import com.microsoft.z3.Sort;

public class Column {
    public String name;
    public Sort type;
    public Constraint constraint;

    public Column(String name, Sort type, Constraint constraint) {
        this.name = name;
        this.type = type;
        this.constraint = constraint;
    }
}
