/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import org.keyproject.key.api.data.KeyIdentifications.TermActionId;

/**
 * This class represents an action that can be executed on a term.
 *
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record TermActionDesc(
        /**
         * Unique identification
         */
        TermActionId commandId,
        /**
         * A string to display to the user.
         */
        String displayName,
        /**
         * Long description of the action for the user.
         */
        String description,
        /**
         * A string identifying a category
         */
        String category,
        /**
         * Kind of the action
         */
        TermActionKind kind) implements KeYDataTransferObject {
}
