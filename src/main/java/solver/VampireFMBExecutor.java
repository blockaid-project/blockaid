package solver;

import com.microsoft.z3.Solver;

import java.util.concurrent.CountDownLatch;

public class VampireFMBExecutor extends SMTExecutor {
    private static String[] command = new String[]{
            "term_to_kill",
            "vampire",
            "--input_syntax", "smtlib2",
            "--proof", "off",
            "--output_mode", "smtcomp",
            "--saturation_algorithm", "fmb",
    };

    public VampireFMBExecutor(String solver, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive) {
        super(solver, latch, command, satConclusive, unsatConclusive);
    }
}
