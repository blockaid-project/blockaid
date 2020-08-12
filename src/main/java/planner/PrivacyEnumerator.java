package planner;

import org.apache.calcite.linq4j.Enumerator;

/**
 * Created by rajatv on 2/16/15.
 */
class PrivacyEnumerator implements Enumerator<Object> {
    /**
     * Returns an array of integers {0, ..., n - 1}.
     */
    static int[] identityList(int n) {
        int[] integers = new int[n];
        for (int i = 0; i < n; i++) {
            integers[i] = i;
        }
        return integers;
    }

    PrivacyEnumerator() {
    }

    public Object current() {
        return null;
    }

    public boolean moveNext() {
        return false;
    }

    public void reset() {
        throw new UnsupportedOperationException();
    }

    public void close() {
    }
}
