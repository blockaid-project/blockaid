package util;

import java.util.*;
import java.util.stream.Collectors;

public class UnionFind<T> {
    private Map<T, Integer> index;
    private List<T> values;
    private int[] root;
    private int[] rank;

    public UnionFind(Collection<T> values) {
        this.values = new ArrayList<>(values);
        this.index = new HashMap<>();
        for (T value : values) {
            this.index.put(value, this.index.size());

        }
        this.root = new int[this.index.size()];
        this.rank = new int[this.index.size()];
        for (int i = 0; i < this.index.size(); ++i) {
            this.root[i] = i;
            this.rank[i] = 0;
        }
    }

    public T find(T value) {
        return values.get(find(index.get(value)));
    }

    private int find(int value) {
        int r = root[value];
        while (r != root[r]) {
            r = root[r];
        }
        while (value != r) {
            int n = root[value];
            root[value] = r;
            value = n;
        }
        return r;
    }

    public void union(T a, T b) {
        union(index.get(a), index.get(b));
    }

    private void union(int a, int b) {
        int ra = find(a);
        int rb = find(b);
        if (ra == rb) {
            return;
        }
        if (rank[ra] < rank[rb]) {
            root[ra] = rb;
        } else if (rank[ra] > rank[rb]) {
            root[rb] = ra;
        } else {
            root[ra] = rb;
            ++rank[rb];
        }
    }
}
