package util;

import java.util.Objects;
import java.util.function.Supplier;

import static util.TerminalColor.ANSI_RESET;

public class Logger {
    public static final boolean USE_COLORS = Objects.equals(System.getProperty("privoxy.use_colors"), "true");
    public static final boolean QUIET = Objects.equals(System.getProperty("privoxy.quiet"), "true");

    public static void printMessage(String message) {
        if (!QUIET) {
            System.out.println(message);
        }
    }

    public static void printStylizedMessage(String message, String style) {
        if (!QUIET) {
            if (USE_COLORS) {
                message = style + message + ANSI_RESET;
            }
            printMessage(message);
        }
    }

    public static void printMessage(Supplier<String> mkMessage) {
        if (!QUIET) {
            System.out.println(mkMessage.get());
        }
    }

    public static void printStylizedMessage(Supplier<String> mkMessage, String style) {
        if (!QUIET) {
            printStylizedMessage(mkMessage.get(), style);
        }
    }
}
