/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
        List<MessageActionItem> actions) {
}
