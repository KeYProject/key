/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import org.key_project.logic.SyntaxElement;

/**
 * Terminal program element. taken from COMPOST and changed to achieve an immutable structure
 */

public interface TerminalProgramElement extends ProgramElement {
    @Override
    default int getSyntaxChildCount() {
        return 0;
    }

    @Override
    default SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Program element " + this + " has no children");
    }
}
