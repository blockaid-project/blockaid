package edu.berkeley.cs.netsys.privacy_proxy.util;

import java.util.Objects;

/* Global options. */
public class Options {
    /* If relation size is greater than this threshold, concrete relation containment uses quantifiers. */
    public static final int CONTAINMENT_USE_QUANTIFIER_THRESHOLD = Integer.parseInt(System.getProperty("privoxy.containment_use_quantifier_threshold", Integer.toString(Integer.MAX_VALUE)));

    /* Cache compliant queries using decision templates. */
    public static boolean ENABLE_CACHING = Objects.equals(System.getProperty("privoxy.enable_caching"), "true");

    /* Generate decision templates but don't store them. */
    public static final boolean CACHE_NO_RETAIN = Objects.equals(System.getProperty("privoxy.cache_no_retain"), "true");

    /* Clear decision cache at trace reset. */
    public static final boolean CLEAR_CACHE_AT_RESET = Objects.equals(System.getProperty("privoxy.clear_cache_at_reset"), "true");

    /* Skip checking and return compliant for every query (but still parses and transforms queries). */
    public static final boolean SKIP_CHECKING = Objects.equals(System.getProperty("privoxy.skip_checking"), "true");

    /* Print formulas to file. */
    public static final boolean PRINT_FORMULAS = Objects.equals(System.getProperty("privoxy.print_formulas"), "true");

    /* Where to store formulas.  */
    public static final String FORMULA_DIR = System.getenv("PRIVOXY_FORMULA_PATH");

    /* Whether to use colors in log messages. */
    public static final boolean USE_COLORS = Objects.equals(System.getProperty("privoxy.use_colors"), "true");

    /* Quiet mode -- suppress log messages. */
    public static final boolean QUIET = Objects.equals(System.getProperty("privoxy.quiet"), "true");

    /* Enable quick denial check -- off by default since denials are not performance-sensitive. */
    public static final boolean ENABLE_QUICK_DENIAL = Objects.equals(System.getProperty("privoxy.enable_quick_denial"), "true");

    /* Disable quantifier elimination optimization. */
    public static final boolean DISABLE_QE = Objects.equals(System.getProperty("privoxy.disable_qe"), "true");

    /* Disable preamble pruning in decision template generation. */
    public static final boolean DISABLE_PREAMBLE_PRUNE = Objects.equals(System.getProperty("privoxy.disable_preamble_prune"), "true");
}
