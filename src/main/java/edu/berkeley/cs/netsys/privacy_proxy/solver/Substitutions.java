package edu.berkeley.cs.netsys.privacy_proxy.solver;

import com.google.common.collect.Maps;

import java.util.*;

// Not very efficient.
class Substitutions<T> {
    private final Map<T, T> map;

    public Substitutions(Collection<T> universe) {
        this.map = new HashMap<>();
        for (T e : universe) {
            map.put(e, e);
        }
    }

    public void set(T from, T to) {
        for (Map.Entry<T, T> entry: map.entrySet()) {
            if (entry.getValue().equals(from)) {
                entry.setValue(to);
            }
        }
    }

    Set<Map.Entry<T, T>> entrySet() {
        return Collections.unmodifiableSet(map.entrySet());
    }

    T get(T from) {
        return map.get(from);
    }

    @Override
    public String toString() {
        return Maps.filterEntries(map, e -> !e.getKey().equals(e.getValue())).toString();
    }
}
