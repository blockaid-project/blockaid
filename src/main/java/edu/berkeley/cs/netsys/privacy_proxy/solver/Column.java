package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.microsoft.z3.Sort;

public record Column(String name, Sort type) {}
