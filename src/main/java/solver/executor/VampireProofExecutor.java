package solver.executor;

import com.google.common.collect.ObjectArrays;
import com.microsoft.z3.Status;

import java.util.concurrent.CountDownLatch;

// TODO(zhangwen): this is ugly.
public class VampireProofExecutor extends ProcessSMTExecutor {
    private static final String[] COMMAND = new String[]{
            "term_to_kill",
            "vampire",
            "--input_syntax", "smtlib2",
//            "--mode", "casc",
//            "--cores", "8",
    };

    public VampireProofExecutor(String name, String smtString, CountDownLatch latch, String config) {
        super(name, smtString, latch,
                ObjectArrays.concat(
                        COMMAND, new String[]{"--decode", config},
                        String.class
                ), true, true, true, false);
    }

    @Override
    protected Status doRunNormal() {
        String output = doRunRaw();
        if (output == null) {
            return Status.UNKNOWN;
        }
        if (output.contains("Termination reason: Satisfiable\n")) {
            return Status.SATISFIABLE;
        }
        if (output.contains("Termination reason: Refutation\n")) {
            return Status.UNSATISFIABLE;
        }
        return Status.UNKNOWN;
    }
}
