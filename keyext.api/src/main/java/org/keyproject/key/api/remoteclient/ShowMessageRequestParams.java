package org.keyproject.key.api.remoteclient;

import java.util.List;

public record ShowMessageRequestParams(
        /**
         * The message type. See {@link MessageType}
         */
        MessageType type,

        /**
         * The actual message
         */
        String message,

        /**
         * The message action items to present.
         *
         */
        List<MessageActionItem> actions
) {
}