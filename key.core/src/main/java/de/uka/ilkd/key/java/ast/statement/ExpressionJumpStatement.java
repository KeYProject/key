/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.ExpressionContainer;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Expression jump statement.
 */
public abstract class ExpressionJumpStatement extends JumpStatement implements ExpressionContainer {
    /**
     * Expression.
     */
    protected final Expression expression;

    /**
     * Expression jump statement.
     */
    public ExpressionJumpStatement() {
        expression = null;
    }

    /**
     * Expression jump statement.
     *
     * @param expr an Expression used to jump
     */
    public ExpressionJumpStatement(Expression expr) {
        expression = expr;
    }

    public ExpressionJumpStatement(@Nullable PositionInfo pi, @Nullable List<Comment> comments,
                                   Expression expression) {
        super(pi, comments);
        this.expression = expression;
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */
    public int getExpressionCount() {
        return (expression != null) ? 1 : 0;
    }

    /**
     * Return the expression at the specified index in this node's "virtual" expression array.
     *
     * @param index an index for an expression.
     * @return the expression with the given index.
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    public Expression getExpressionAt(int index) {
        if (expression != null && index == 0) {
            return expression;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get expression.
     *
     * @return the expression.
     */
    public Expression getExpression() {
        return expression;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        return (expression != null) ? 1 : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (expression != null) {
            if (index == 0) {
                return expression;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }
}
