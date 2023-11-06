/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression;

import recoder.java.Expression;
import recoder.java.NonTerminalProgramElement;
import recoder.java.StatementContainer;

/**
 * An assignment is an operator with side-effects.
 */

public abstract class Assignment extends Operator implements ExpressionStatement {

    /**
     * either statementParent or expressionParent is null, in case of ambiguities (e.g. Assignment
     * as a parent), prefer an ExpressionContainer as parent. We could resolve these problems by
     * introduction of an AssignmentContainer as supertype of StatementContainer and
     * ExpressionContainer.
     */

    protected StatementContainer statementParent;

    /**
     * Assignment.
     */

    public Assignment() {
        // nothing to do
    }

    /**
     * Assignment.
     *
     * @param unaryChild an expression.
     */

    public Assignment(Expression unaryChild) {
        super(unaryChild);
    }

    /**
     * Assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public Assignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    /**
     * Assignment.
     *
     * @param proto an assignment.
     */

    protected Assignment(Assignment proto) {
        super(proto);
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        if (expressionParent != null) {
            return expressionParent;
        } else {
            return statementParent;
        }
    }

    /**
     * Get statement container.
     *
     * @return the statement container.
     */

    public StatementContainer getStatementContainer() {
        return statementParent;
    }

    /**
     * Set statement container.
     *
     * @param c a statement container.
     */

    public void setStatementContainer(StatementContainer c) {
        statementParent = c;
    }

    /**
     * Checks if this operator is left or right associative. Assignments are right associative.
     *
     * @return <CODE>true</CODE>, if the operator is left associative, <CODE>
     * false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return false;
    }

    public abstract Assignment deepClone();
}
