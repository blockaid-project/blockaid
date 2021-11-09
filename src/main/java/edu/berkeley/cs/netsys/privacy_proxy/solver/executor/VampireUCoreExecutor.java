package edu.berkeley.cs.netsys.privacy_proxy.solver.executor;

import com.google.common.collect.ObjectArrays;

import java.util.concurrent.CountDownLatch;

// TODO(zhangwen): this is ugly.
public class VampireUCoreExecutor extends ProcessSMTExecutor {
    private static final String[] COMMAND = new String[]{
            "term_to_kill",
            "vampire",
            "--ignore_missing_inputs_in_unsat_core", "on",
            "--input_syntax", "smtlib2",
    };

    public VampireUCoreExecutor(String name, String smtString, CountDownLatch latch, String config) {
        super(name, smtString, latch,
                ObjectArrays.concat(
                        COMMAND, new String[]{"--decode", config},
                        String.class
                ), true, true, false, true);
    }
}
