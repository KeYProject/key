/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;

import org.key_project.util.ExtList;

/**
 * Branch.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class BranchImp extends JavaNonTerminalProgramElement implements Branch {

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children
     *        the children of this AST element as KeY classes. May contain: Comments
     */
    public BranchImp(ExtList children) {
        super(children);
    }


    public BranchImp() {
        super();
    }


    public BranchImp(ExtList children, PositionInfo pos) {
        super(children, pos);
    }


    public BranchImp(PositionInfo pi, List<Comment> comments) {
        super(pi, comments);
    }
}