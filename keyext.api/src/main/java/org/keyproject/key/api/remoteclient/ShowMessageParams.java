/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteclient;

/**
 * @param type The message type. See {@link MessageType}.
 * @param message the actual message
 */
public record ShowMessageParams(MessageType type, String message) {
}
