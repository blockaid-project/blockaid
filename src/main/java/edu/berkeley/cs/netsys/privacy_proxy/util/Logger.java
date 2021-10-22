package edu.berkeley.cs.netsys.privacy_proxy.util;

import java.util.function.Supplier;

import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.QUIET;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.USE_COLORS;
import static edu.berkeley.cs.netsys.privacy_proxy.util.TerminalColor.ANSI_RESET;

public class Logger {
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
