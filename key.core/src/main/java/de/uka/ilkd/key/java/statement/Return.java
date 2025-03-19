/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Return.
 *
 */

public class Return extends ExpressionJumpStatement {


    /**
     * Expression jump statement.
     *
     * @param expr an Expression used to jump
     */
    public Return(Expression expr) {
        super(expr);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: an Expression
     *        (as expression of the ExpressionJumpStatement), Comments
     */
    public Return(ExtList children) {
        super(children);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnReturn(this);
    }
}
