/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import org.keyproject.key.api.data.KeyIdentifications.TermActionId;

/**
 * This class represents an action that can be executed on a term.
 *
 * @param commandId Unique identification
 * @param displayName A string to display to the user.
 * @param description Long description of the action for the user.
 * @param category A string identifying a category
 * @param kind Kind of the action
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record TermActionDesc(
        TermActionId commandId,
        String displayName,
        String description,
        String category,
        TermActionKind kind) implements KeYDataTransferObject {
}
