package edu.berkeley.cs.netsys.privacy_proxy.sql;

/**
 * Catch all Exception thrown by code in quark-calcite.
 */
public class PrivacyException extends Exception {
    public PrivacyException(String message) {
        super(message);
    }

    public PrivacyException(Throwable cause) {
        super(cause);
    }
}