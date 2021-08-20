package cache;

import java.util.ArrayList;
import java.util.HashMap;

public class PushPopMap<K, V> {
    private final HashMap<K, V> map = new HashMap<>();
    private final ArrayList<ArrayList<K>> keys = new ArrayList<>();

    public PushPopMap() {
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
        return true;
    }

    public void pop() {
        ArrayList<K> last = keys.remove(keys.size() - 1);
        for (K key : last) {
            map.remove(key);
        }
    }
}
