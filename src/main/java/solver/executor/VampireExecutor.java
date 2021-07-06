package solver.executor;

import java.util.concurrent.CountDownLatch;

public abstract class VampireExecutor extends ProcessSMTExecutor {
    protected static final String[] BASE_COMMAND = new String[]{
            "term_to_kill",
            "vampire",
            "--input_syntax", "smtlib2",
            "--proof", "off",
            "--output_mode", "smtcomp",
    };

    protected VampireExecutor(String name, String smtString, CountDownLatch latch, String[] command, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive) {
        super(name, smtString, latch, command, satConclusive, unsatConclusive, unknownConclusive);
    }
}
