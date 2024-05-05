/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import org.jspecify.annotations.Nullable;

/**
 * Classes with this interface provides a simple human-readable String where they came from.
 *
 * @author Alexander Weigl
 * @version 1 (12/30/21)
 */
public interface HasOrigin {
    /**
     * Information about the origin of the rule.
     * <p>
     * Should be a human-readable location where the user can find the declaration of the rule.
     * <p>
     * This field is set by the parser with [url]:[lineNumber]
     */
    default @Nullable String getOrigin() {
        return null;
    }
}
