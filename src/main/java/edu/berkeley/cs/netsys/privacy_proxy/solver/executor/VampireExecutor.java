package edu.berkeley.cs.netsys.privacy_proxy.solver.executor;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ObjectArrays;

import java.util.concurrent.CountDownLatch;

public class VampireExecutor extends ProcessSMTExecutor {
    public VampireExecutor(String name, String config, String smtString, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive) {
        super(name, smtString, latch,
                ImmutableList.of(
                        "term_to_kill",
                        "vampire",
                        "--input_syntax", "smtlib2",
                        "--output_mode", "smtcomp",
                        "--decode", config
                ), satConclusive, unsatConclusive, unknownConclusive, false);
    }
}
