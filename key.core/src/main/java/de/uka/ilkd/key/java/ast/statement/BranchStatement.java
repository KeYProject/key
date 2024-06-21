/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;

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
     * @param children
     *        the children of this AST element as KeY classes. May contain: Comments
     */
    public BranchStatement(ExtList children) {
        super(children);
    }

    public BranchStatement(PositionInfo pi, List<Comment> comments) {
        super(pi, comments);
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
