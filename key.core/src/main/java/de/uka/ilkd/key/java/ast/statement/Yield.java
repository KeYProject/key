/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * A {@code yield} statement (JLS 14.21), used inside an arm of a switch expression to provide
 * the value of the switch expression.
 */
public class Yield extends ExpressionJumpStatement {

    /**
     * Creates a yield statement.
     *
     * @param expr the yielded expression
     */
    public Yield(Expression expr) {
        super(expr);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes; may contain an
     *        {@link Expression} and {@link Comment}s
     */
    public Yield(ExtList children) {
        super(children);
    }

    /**
     * Creates a yield statement with source information.
     *
     * @param expr the yielded expression
     * @param pi the position information
     * @param comments the comments attached to this statement
     */
    public Yield(Expression expr, PositionInfo pi, List<Comment> comments) {
        super(expr, pi, comments);
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnYield(this);
    }
}
