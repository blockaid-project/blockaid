package solver.executor;

import com.google.common.collect.ObjectArrays;

import java.util.concurrent.CountDownLatch;

public class VampireOttExecutor extends VampireExecutor {
    protected static final String[] COMMAND = ObjectArrays.concat(
            BASE_COMMAND, new String[]{
                    "--decode",
                    "ott+1_8:1_add=large:afp=10000:afq=1.0:amm=sco:anc=none:bd=off:bsr=on:fsr=off:fde=unused:ile=on:irw=on:nm=0:newcnf=on:nwc=1:sas=z3:sp=occurrence:updr=off:uhcvi=on_10000"
            }, String.class);

    public VampireOttExecutor(String name, String smtString, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive) {
        super(name, smtString, latch, COMMAND, satConclusive, unsatConclusive);
    }
}
