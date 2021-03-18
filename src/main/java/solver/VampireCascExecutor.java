package solver;

import com.microsoft.z3.Solver;

import java.util.concurrent.CountDownLatch;

public class VampireCascExecutor extends SMTExecutor {
    private static String[] command = new String[]{
            "term_to_kill",
            "vampire",
            "--input_syntax", "smtlib2",
            "--proof", "off",
            "--output_mode", "smtcomp",
            "--mode", "portfolio",
            "--schedule", "casc",
    };

    public VampireCascExecutor(String solver, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive) {
        super(solver, latch, command, satConclusive, unsatConclusive);
    }
}
