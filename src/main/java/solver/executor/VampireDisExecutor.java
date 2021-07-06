package solver.executor;

import com.google.common.collect.ObjectArrays;

import java.util.concurrent.CountDownLatch;

public class VampireDisExecutor extends VampireExecutor {
    protected static final String[] COMMAND = ObjectArrays.concat(
            BASE_COMMAND, new String[]{
                    "--decode",
                    "dis+11_32_add=large:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:er=filter:ile=on:lcm=predicate:lma=on:newcnf=on:nwc=5:sp=occurrence:updr=off_10000"
            }, String.class);

    public VampireDisExecutor(String name, String smtString, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive) {
        super(name, smtString, latch, COMMAND, satConclusive, unsatConclusive, unknownConclusive);
    }
}
