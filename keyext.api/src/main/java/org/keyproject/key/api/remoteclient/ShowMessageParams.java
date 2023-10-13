package org.keyproject.key.api.remoteclient;

public record ShowMessageParams(
        /**
         * The message type. See {@link MessageType}.
         */
        MessageType type,

        /**
         * The actual message.
         */
        String message) {
    
}
