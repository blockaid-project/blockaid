package edu.berkeley.cs.netsys.privacy_proxy.solver.executor;

import com.google.common.collect.ImmutableList;

import java.util.function.Consumer;

// TODO(zhangwen): this is ugly.
public class VampireUCoreExecutor extends ProcessSMTExecutor {
    private static ImmutableList<String> makeCommand(String config) {
        return ImmutableList.of(
                "term_to_kill",
                "vampire",
                "--ignore_missing_inputs_in_unsat_core", "on",
                "--input_syntax", "smtlib2",
                "--decode", config
        );
    }

    public VampireUCoreExecutor(String name, String smtString, Consumer<String> signalFunc, String config) {
        super(name, smtString, signalFunc, makeCommand(config), true, true, false, true);
    }
}
