package util;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class UnionFind<T> {
    private final ImmutableMap<T, Integer> index;
    private final ImmutableList<T> elements;
    private final int[] root;
    private final int[] rank;
    private final int[] size; // Size of the equivalence class rooted at each element.
    private final Object[] data; // Data associated with each equivalence class; null means no data.

    public UnionFind(Collection<T> elements) {
        this.elements = ImmutableList.copyOf(elements);

        ImmutableMap.Builder<T, Integer> indexBuilder = new ImmutableMap.Builder<>();
        for (int i = 0; i < this.elements.size(); ++i) {
            indexBuilder.put(this.elements.get(i), i);
        }
        this.index = indexBuilder.build();

        this.root = new int[this.index.size()];
        this.size = new int[this.index.size()];
        for (int i = 0; i < this.index.size(); ++i) {
            this.root[i] = i;
            this.size[i] = 1;
        }
        this.rank = new int[this.index.size()];
        this.data = new Object[this.index.size()];
    }

    public T find(T element) {
        checkArgument(index.containsKey(element));
        return elements.get(findIdx(index.get(element)));
    }

    public EquivalenceClass findComplete(T element) {
        checkArgument(index.containsKey(element));
        int rootIdx = findIdx(index.get(element));
        return new EquivalenceClass(elements.get(rootIdx), data[rootIdx], size[rootIdx]);
    }

    public void attachData(T element, Object datum) {
        checkArgument(index.containsKey(element));
        checkNotNull(datum, "union find data must be non-null");
        int rootIdx = findIdx(index.get(element));

        Object oldDatum = data[rootIdx];
        if (oldDatum != null) {
            checkArgument(datum.equals(oldDatum),
                    "conflicting union find data: " + datum + ", " + oldDatum);
            return;
        }
        data[rootIdx] = datum;
    }

    private int findIdx(int elemIdx) {
        int r = root[elemIdx];
        while (r != root[r]) {
            r = root[r];
        }
        while (elemIdx != r) {
            int n = root[elemIdx];
            root[elemIdx] = r;
            elemIdx = n;
        }
        return r;
    }

    public void union(T a, T b) {
        checkArgument(index.containsKey(a));
        checkArgument(index.containsKey(b));
        unionIdx(index.get(a), index.get(b));
    }

    private void unionIdx(int a, int b) {
        int ra = findIdx(a);
        int rb = findIdx(b);
        if (ra == rb) {
            return;
        }
        checkArgument(data[ra] == null || data[rb] == null || data[ra].equals(data[rb]),
                "conflicting union find data: " + data[ra] + ", " + data[rb]);
        Object datum = (data[ra] != null) ? data[ra] : data[rb];

        if (rank[ra] < rank[rb]) {
            root[ra] = rb;
            size[rb] += size[ra];
            data[rb] = datum;
        } else if (rank[ra] > rank[rb]) {
            root[rb] = ra;
            size[ra] += size[rb];
            data[ra] = datum;
        } else {
            root[ra] = rb;
            size[rb] += size[ra];
            data[rb] = datum;
            ++rank[rb];
        }
    }

    public List<T> getRoots() {
        return IntStream.range(0, index.size())
                .filter(i -> root[i] == i)
                .mapToObj(elements::get)
                .collect(Collectors.toList());
    }

    @Override
    public String toString() {
        ArrayListMultimap<Integer, Integer> root2Elems = ArrayListMultimap.create();
        for (int i = 0; i < index.size(); ++i) {
            root2Elems.put(findIdx(i), i);
        }

        StringBuilder sb = new StringBuilder();
        for (Integer rootIdx: root2Elems.keySet()) {
            List<Integer> elemIndices = root2Elems.get(rootIdx);
            Object datum = data[rootIdx];

            // Only print if (1) the equivalence class has >= 2 elements, or (2) there is associated data.
            if (elemIndices.size() < 2 && datum == null) {
                continue;
            }

            sb.append("{");
            sb.append(elemIndices.stream()
                    .map(i -> elements.get(i).toString())
                    .collect(Collectors.joining(", ")));
            sb.append("}");
            if (datum != null) {
                sb.append(": ").append(datum);
            }
            sb.append("\n");
        }
        return sb.toString();
    }

    public class EquivalenceClass {
        private final T root;
        private final Object datum;
        private final int size;

        public EquivalenceClass(T root, Object datum, int size) {
            this.root = root;

            this.datum = datum;
            this.size = size;
        }

        public T getRoot() {
            return root;
        }

        public Object getDatum() {
            return datum;
        }

        public int getSize() {
            return size;
        }
    }
}
