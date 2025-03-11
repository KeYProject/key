/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.NonTerminalProgramElement;

import org.key_project.util.ExtList;

/**
 * Branch statement.
 *
 * @author AL
 * @author <TT>AutoDoc</TT>
 */

public abstract class BranchStatement extends JavaStatement implements NonTerminalProgramElement {

    public BranchStatement() {

    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments
     */
    public BranchStatement(ExtList children) {
        super(children);
    }

    /**
     * Get the number of branches in this container.
     *
     * @return the number of branches.
     */

    public abstract int getBranchCount();

    /*
     * Return the branch at the specified index in this node's "virtual" branch array.
     *
     * @param index an index for a branch.
     *
     * @return the branch with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */

    public abstract Branch getBranchAt(int index);
}
