package org.keyproject.key.api.remoteclient;

record LogMessageParams(
        /**
         * The message type. See {@link MessageType}
         */
        MessageType type,

        /**
         * The actual message
         */
        String message
) {

}
