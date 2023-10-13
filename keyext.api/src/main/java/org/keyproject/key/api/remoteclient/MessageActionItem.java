package org.keyproject.key.api.remoteclient;

public record MessageActionItem(
        /**
         * A short title like 'Retry', 'Open Log' etc.
         */
        String title
) {
}