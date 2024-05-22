/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

/**
 * Non terminal program element. taken from COMPOST and changed to achieve an immutable structure
 */

public interface NonTerminalProgramElement extends ProgramElement {

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    int getChildCount();

    /**
     * Returns the child at the specified index in this node's "virtual" child array.
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    ProgramElement getChildAt(int index);

}
