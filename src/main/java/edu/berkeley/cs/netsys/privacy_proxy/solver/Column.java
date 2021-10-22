package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.Sort;

public class Column {
    public final String name;
    public final Sort type;

    public Column(String name, Sort type) {
        this.name = name;
        this.type = type;
    }
}
