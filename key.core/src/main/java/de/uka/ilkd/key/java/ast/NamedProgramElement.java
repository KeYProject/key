/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast;


import de.uka.ilkd.key.logic.ProgramElementName;

/**
 * Named program element. taken from COMPOST and changed to achieve an immutable structure
 */

public interface NamedProgramElement extends NamedModelElement, NonTerminalProgramElement {

    /**
     * Get identifier.
     *
     * @return the identifier.
     */
    ProgramElementName getProgramElementName();

}
