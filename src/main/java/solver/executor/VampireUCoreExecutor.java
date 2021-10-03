package solver.executor;

import com.google.common.collect.ObjectArrays;
import com.microsoft.z3.Status;

import java.util.concurrent.CountDownLatch;

// TODO(zhangwen): this is ugly.
public class VampireUCoreExecutor extends ProcessSMTExecutor {
    private static final String[] COMMAND = new String[]{
            "term_to_kill",
            "vampire",
            "--input_syntax", "smtlib2",
    };

    public VampireUCoreExecutor(String name, String smtString, CountDownLatch latch, String config) {
        super(name, smtString, latch,
                ObjectArrays.concat(
                        COMMAND, new String[]{"--decode", config},
                        String.class
                ), true, true, true, true);
    }
}
