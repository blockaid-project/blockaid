package solver.executor;

import java.util.concurrent.CountDownLatch;

// TODO(zhangwen): this is ugly.
public class VampireCASCProofExecutor extends ProcessSMTExecutor {
    private static final String[] COMMAND = new String[]{
            "term_to_kill",
            "vampire",
            "--input_syntax", "smtlib2",
            "--mode", "casc",
            "--cores", "8",
            "--time_limit", "2s"
//            "--decode",
//            "lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_10000"
    };

    public VampireCASCProofExecutor(String name, String smtString, CountDownLatch latch) {
        super(name, smtString, latch, COMMAND, false, false, false, false);
    }
}
