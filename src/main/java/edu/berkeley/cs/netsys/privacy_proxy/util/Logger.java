package edu.berkeley.cs.netsys.privacy_proxy.util;

import java.util.function.Supplier;

import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.LOG_LEVEL;
import static edu.berkeley.cs.netsys.privacy_proxy.util.Options.USE_COLORS;
import static edu.berkeley.cs.netsys.privacy_proxy.util.TerminalColor.ANSI_RESET;

public class Logger {
    public static void printMessage(String message) {
        printMessage(message, LogLevel.NORMAL);
    }

    public static void printMessage(String message, LogLevel level) {
        if (LOG_LEVEL.isAtLeast(level)) {
            System.out.println(message);
        }
    }

    public static void printStylizedMessage(String message, String style) {
        printStylizedMessage(message, style, LogLevel.NORMAL);
    }

    public static void printStylizedMessage(String message, String style, LogLevel level) {
        if (LOG_LEVEL.isAtLeast(level)) {
            if (USE_COLORS) {
                message = style + message + ANSI_RESET;
            }
            printMessage(message);
        }
    }

    public static void printMessage(Supplier<String> mkMessage) {
        printMessage(mkMessage, LogLevel.NORMAL);
    }

    public static void printMessage(Supplier<String> mkMessage, LogLevel level) {
        if (LOG_LEVEL.isAtLeast(level)) {
            System.out.println(mkMessage.get());
        }
    }

    public static void printStylizedMessage(Supplier<String> mkMessage, String style) {
        printStylizedMessage(mkMessage, style, LogLevel.NORMAL);
    }

    public static void printStylizedMessage(Supplier<String> mkMessage, String style, LogLevel level) {
        if (LOG_LEVEL.isAtLeast(level)) {
            printStylizedMessage(mkMessage.get(), style);
        }
    }
}
