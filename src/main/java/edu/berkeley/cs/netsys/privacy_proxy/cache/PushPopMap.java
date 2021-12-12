package edu.berkeley.cs.netsys.privacy_proxy.cache;

import edu.berkeley.cs.netsys.privacy_proxy.solver.context.Z3ContextWrapper;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.function.BiFunction;

public class PushPopMap<K, V> {
    private final HashMap<K, V> map = new HashMap<>();
    private final ArrayList<ArrayList<K>> keys = new ArrayList<>();
    private final BiFunction<Map<K, V>, K, Boolean> check;

    public PushPopMap(BiFunction<Map<K, V>, K, Boolean> check) {
        this.check = check;
        keys.add(new ArrayList<>());
    }

    public void push() {
        keys.add(new ArrayList<>());
    }

    // Does not allow null value -- here we're checking equality `x1 = x2`, which is not true when x1 or x2 is null.
    // FIXME(zhangwen): allow "NOT NULL" labels in decision cache?
    public boolean ensureMapping(K key, V value) {
        if (value == null) {
            return false;
        }
        if (map.containsKey(key)) {
            return Z3ContextWrapper.normalizedEquals(map.get(key), value);
        }

        keys.get(keys.size() - 1).add(key);
        map.put(key, value);
        return check.apply(Collections.unmodifiableMap(map), key);
    }

    public void pop() {
        ArrayList<K> last = keys.remove(keys.size() - 1);
        for (K key : last) {
            map.remove(key);
        }
    }
}
