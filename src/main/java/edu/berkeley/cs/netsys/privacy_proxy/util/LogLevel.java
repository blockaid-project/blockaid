package edu.berkeley.cs.netsys.privacy_proxy.util;

public enum LogLevel {
    QUIET(0),
    NORMAL(1),
    VERBOSE(2);

    private final int value;

    LogLevel(int value) {
        this.value = value;
    }

    public boolean isAtLeast(LogLevel other) {
        return value >= other.value;
    }

    static LogLevel fromString(String s) {
        return switch (s) {
            case "quiet" -> QUIET;
            case "normal" -> NORMAL;
            case "verbose" -> VERBOSE;
            default -> throw new IllegalArgumentException("Unknown log level: " + s);
        };
    }
}
