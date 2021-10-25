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

    public enum OnOffType {
        ON,
        OFF;
    }

    private static OnOffType getOnOffProperty(String key, OnOffType def) {
        String value = System.getProperty(key);
        if (value == null) {
            return def;
        }
        return switch (value) {
            case "on" -> OnOffType.ON;
            case "off" -> OnOffType.OFF;
            default -> throw new IllegalArgumentException(
                    "unrecognized option for " + key + " (must be on/off): " + value);
        };
    }

    /* Disable preamble pruning in decision template generation. */
    /**
     * FIXME(zhangwen): Preamble pruning is now disabled by default because it may necessitate dis-equalities in
     *  decision templates, which is currently not supported.  Here's an example:
     *  - Imported dependency: If I receive a notification about a post, then (1) then post if public,
     *      (2) the post is shared with me, or (3) the post is authored by me.
     *  - Primary key: `posts`.`id`, `people`.`id`.
     *  - Views: I'm allowed to view mentions on posts shared with me.
     *  - Trace: (1) My person ID is `x`,  (2) I received a notification about post `y`, (2) post `y`
     *      is _NOT_ public and its author is _NOT_ `y`.
     *  The two dis-equalities, in conjunction with te imported dependency, imply that the post must be
     *  shared with me, and therefore I'm allowed to view its mentions.  The dis-equalities would not have been
     *  necessary if we had kept the views that (1) allow viewing my own posts, and (2) allow viewing public posts.
     */
    public static final OnOffType PRUNE_PREAMBLE = getOnOffProperty("privoxy.prune_preamble", OnOffType.OFF);

    public enum BoundedFormulaType {
        THEORY, // Use ints and bools for database column types.
        CUSTOM_SORTS; // Use custom sorts (like in unbounded formula).

        private static BoundedFormulaType parse(String s) {
            return switch (s) {
                case "theory" -> THEORY;
                case "custom_sorts" -> CUSTOM_SORTS;
                default -> throw new IllegalArgumentException("unrecognized bounded formula type: " + s);
            };
        }
    }

    /* Use custom sorts (instead of ints and bools) in bounded formula. */
    public static final BoundedFormulaType BOUNDED_FORMULA_TYPE =
            BoundedFormulaType.parse(System.getProperty("privoxy.bounded_formula_type", "theory"));
}