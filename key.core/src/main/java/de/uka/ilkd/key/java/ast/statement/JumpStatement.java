/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;

import org.key_project.util.ExtList;

/**
 * Jump statement.
 *
 * @author <TT>AutoDoc</TT>
 */
public abstract class JumpStatement extends JavaStatement {

    /**
     * Jump statement.
     *
     * @param children
     *        the children of this AST element as KeY classes. May contain: Comments
     */
    public JumpStatement(ExtList children) {
        super(children);
    }


    /**
     * Jump statement.
     */
    public JumpStatement() {}

    public JumpStatement(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }
}
