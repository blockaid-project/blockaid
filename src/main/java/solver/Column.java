package solver;

import com.microsoft.z3.Sort;

public class Column {
    public String name;
    public Sort type;

    public Column(String name, Sort type) {
        this.name = name;
        this.type = type;
    }
}
