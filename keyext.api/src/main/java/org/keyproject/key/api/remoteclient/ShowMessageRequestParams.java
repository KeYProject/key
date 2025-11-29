/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteclient;

import java.util.List;

/**
 * @param type The message type. See {@link MessageType}.
 * @param message the actual message
 */
public record ShowMessageRequestParams(
        MessageType type, String message, List<MessageActionItem> actions) {
}
