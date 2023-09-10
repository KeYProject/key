/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.ProgramElement;

/**
 * Expression jump statement.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class ExpressionJumpStatement extends JumpStatement implements ExpressionContainer {

    /**
     * Expression.
     */

    protected Expression expression;

    /**
     * Expression jump statement.
     */

    public ExpressionJumpStatement() {
        // nothing to do
    }

    /**
     * Expression jump statement.
     *
     * @param expr an expression.
     */

    public ExpressionJumpStatement(Expression expr) {
        if (expr != null) {
            setExpression(expr);
        }
        // makeParentRoleValid() called by subclasses' constructors
    }

    /**
     * Expression jump statement.
     *
     * @param proto an expression jump statement.
     */

    protected ExpressionJumpStatement(ExpressionJumpStatement proto) {
        super(proto);
        if (proto.expression != null) {
            expression = proto.expression.deepClone();
        }
        // makeParentRoleValid() called by subclasses' constructors
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (expression != null) {
            expression.setExpressionContainer(this);
        }
    }

    /**
     * Replace a single child in the current node. The child to replace is matched by identity and
     * hence must be known exactly. The replacement element can be null - in that case, the child is
     * effectively removed. The parent role of the new child is validated, while the parent link of
     * the replaced child is left untouched.
     *
     * @param p the old child.
     * @param p the new child.
     * @return true if a replacement has occured, false otherwise.
     * @throws ClassCastException if the new child cannot take over the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        if (expression == p) {
            Expression r = (Expression) q;
            expression = r;
            if (r != null) {
                r.setExpressionContainer(this);
            }
            return true;
        }
        return false;
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    public int getExpressionCount() {
        return (expression != null) ? 1 : 0;
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression
     * array. @param index an index for an expression. @return the expression with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
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
     * Set expression.
     *
     * @param expr an expression.
     */

    public void setExpression(Expression expr) {
        expression = expr;
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

    public int getChildPositionCode(ProgramElement child) {
        // role 0: expression
        if (expression == child) {
            return 0;
        }
        return -1;
    }
}
