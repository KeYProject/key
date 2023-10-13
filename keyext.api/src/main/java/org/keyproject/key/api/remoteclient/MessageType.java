package org.keyproject.key.api.remoteclient;

public enum MessageType {
        Unused,
        /**
         * An error message.
         */
        Error,
        /**
         * A warning message.
         */
        Warning,
        /**
         * An information message.
         */
        Info,
        /**
         * A log message.
         */
        Log,
        /**
         * A debug message.
         *
         * @proposed
         * @since 3.18.0
         */
        Debug
    }
