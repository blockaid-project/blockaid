package util;

import java.util.Objects;

public class TerminalColor {
    public static final boolean USE_COLORS = Objects.equals(System.getProperty("privoxy.use_colors"), "true");

    public static final String ANSI_BLUE_BACKGROUND = "\u001B[44m";
    public static final String ANSI_BLACK = "\u001B[30m";
    public static final String ANSI_YELLOW_BACKGROUND = "\u001B[43m";
    public static final String ANSI_RESET = "\u001B[0m";
}
