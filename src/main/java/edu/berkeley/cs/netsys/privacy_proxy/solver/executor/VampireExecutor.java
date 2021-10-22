package edu.berkeley.cs.netsys.privacy_proxy.solver.executor;

import com.google.common.collect.ObjectArrays;

import java.util.concurrent.CountDownLatch;

public class VampireExecutor extends ProcessSMTExecutor {
    protected static final String[] BASE_COMMAND = new String[]{
            "term_to_kill",
            "vampire",
            "--input_syntax", "smtlib2",
            "--output_mode", "smtcomp",
    };

    public VampireExecutor(String name, String config, String smtString, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive) {
        super(name, smtString, latch, ObjectArrays.concat(
                BASE_COMMAND, new String[]{
                        "--decode",
                        config
                }, String.class), satConclusive, unsatConclusive, unknownConclusive, false);
    }
}
