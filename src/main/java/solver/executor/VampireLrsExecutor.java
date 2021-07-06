package solver.executor;

import com.google.common.collect.ObjectArrays;

import java.util.concurrent.CountDownLatch;

public class VampireLrsExecutor extends VampireExecutor {
    protected static final String[] COMMAND = ObjectArrays.concat(
            BASE_COMMAND, new String[]{
                    "--decode",
                    "lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_10000"
            }, String.class);

    public VampireLrsExecutor(String name, String smtString, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive) {
        super(name, smtString, latch, COMMAND, satConclusive, unsatConclusive);
    }
}
