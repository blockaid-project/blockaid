package edu.berkeley.cs.netsys.privacy_proxy.cache;

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

    public boolean ensureMapping(K key, V value) {
        if (map.containsKey(key)) {
            return map.get(key).equals(value);
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
