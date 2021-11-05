package edu.berkeley.cs.netsys.privacy_proxy.util;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Maps;

import java.util.Map;

/**
 * Collection of Vampire configurations we use.
 */
public class VampireConfigurations {
    /**
     * Maps configuration name to string.  Append timeout in integer deciseconds to the configuration string to pass to
     * Vampire.
     */
    private static final ImmutableMap<String, String> nameToConfig = ImmutableMap.<String, String>builder()
            .put("vampire_lrs+10_1", "lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_")
            .put("vampire_dis+11_3", "dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_")
            .put("vampire_dis+3_1",  "dis+3_1_cond=on:fde=unused:nwc=1:sd=1:ss=axioms:st=1.2:sos=on:sac=on:add=off:afp=40000:afq=1.4:anc=none_")
            .put("vampire_dis+1011", "dis+1011_3_cond=fast:ep=R:gs=on:gsem=off:lwlo=on:nm=0:nwc=1:sd=5:ss=axioms:st=1.5:sos=on:sac=on:add=large:afr=on:afp=1000:afq=1.1:anc=none:uhcvi=on_")
            .put("vampire_lrs+11_8", "lrs+11_8:1_add=large:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=fast:gs=on:gsaa=full_model:inw=on:ile=on:lcm=predicate:nm=4:newcnf=on:nwc=1:sp=reverse_arity:tha=off:urr=on_")
//            .put("vampire_lrs+1_3", "lrs+1_3:2_afr=on:afp=100000:afq=1.0:anc=all_dependent:cond=on:fde=none:gs=on:inw=on:ile=on:irw=on:nm=6:nwc=1:stl=30:sos=theory:updr=off:uhcvi=on_")
//            .put("vampire_dis+2_3", "dis+2_3_av=off:cond=on:fsr=off:lcm=reverse:lma=on:nwc=1:sos=on:sp=reverse_arity_")
//            .put("vampire_lrs+1011", "lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:sos=theory:sp=occurrence:urr=ec_only:updr=off_")
//            .put("vampire_lrs+11_20", "ilrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_")
//            .put("vampire_lrs+1_7", "lrs+1_7_av=off:cond=fast:fde=none:gs=on:gsem=off:lcm=predicate:nm=6:nwc=1:stl=30:sd=3:ss=axioms:sos=on:sp=occurrence:updr=off_")
            .build();

    public static Map<String, String> getAll(long timeoutS) {
        return Maps.transformValues(nameToConfig, s -> s + (timeoutS * 10));
    }
}
