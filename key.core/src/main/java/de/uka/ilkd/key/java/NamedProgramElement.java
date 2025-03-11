/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;


/**
 * Named program element. taken from COMPOST and changed to achieve an immutable structure
 */

public interface NamedProgramElement extends NamedModelElement, NonTerminalProgramElement {

    /**
     * Get identifier.
     *
     * @return the identifier.
     */
    de.uka.ilkd.key.logic.ProgramElementName getProgramElementName();

}
