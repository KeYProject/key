/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;


/**
 * Statement container. taken from COMPOST and changed to achieve an immutable structure
 */

public interface StatementContainer extends NonTerminalProgramElement {

    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */
    int getStatementCount();

    /*
     * Return the statement at the specified index in this node's "virtual" statement array.
     *
     * @param index an index for a statement.
     *
     * @return the statement with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    Statement getStatementAt(int index);
}
