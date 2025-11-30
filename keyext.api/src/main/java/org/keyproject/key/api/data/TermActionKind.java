/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

/**
 * Possible kinds of an action applicable to position on a sequent.
 *
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public enum TermActionKind implements KeYDataTransferObject {
    /**
     * Built-In Rule
     */
    BuiltIn,
    /**
     * Proof Script
     */
    Script,
    /**
     * Proof Macro
     */
    Macro,
    /**
     * Taclet
     */
    Taclet
}
