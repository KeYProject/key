/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.declaration.Modifier;


/**
 * Declaration. taken from COMPOST and changed to achieve an immutable structure
 */
public interface Declaration extends NonTerminalProgramElement {

    /**
     * Get the modifiers.
     *
     * @return the (original) list of modifiers wrapped .
     */
    ImmutableArray<Modifier> getModifiers();
}
