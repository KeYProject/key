/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.*;

/**
 * Assert statement of Java 1.4.
 *
 * @author AL
 */

public class Assert extends JavaStatement implements ExpressionContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -5203926244893543507L;

    /**
     * Assertion condition.
     */
    protected Expression condition;

    /**
     * Assertion message.
     */
    protected Expression message;

    /**
     * Trivial constructor.
     */
    public Assert() {
        // nothing to do
    }

    /**
     * Assert.
     *
     * @param cond the condition expression (may not be null).
     */
    public Assert(Expression cond) {
        this(cond, null);
    }

    /**
     * Assert.
     *
     * @param cond the condition expression (may not be null).
     * @param msg the message expression.
     */
    public Assert(Expression cond, Expression msg) {
        if (cond == null) {
            throw new NullPointerException();
        }
        condition = cond;
        message = msg;
        makeParentRoleValid();
    }

    /**
     * Assert.
     *
     * @param proto an assert.
     */
    protected Assert(Assert proto) {
        super(proto);
        if (proto.condition != null) {
            condition = proto.condition.deepClone();
        }
        if (proto.message != null) {
            message = proto.message.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */
    public Assert deepClone() {
        return new Assert(this);
    }

    public SourceElement getLastElement() {
        return (message != null) ? message.getLastElement() : condition.getLastElement();
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (condition != null) {
            result++;
        }
        if (message != null) {
            result++;
        }
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (condition != null) {
            if (index == 0) {
                return condition;
            }
            index--;
        }
        if (message != null) {
            if (index == 0) {
                return message;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: condition
        // role 1: message
        if (condition == child) {
            return 0;
        }
        if (message == child) {
            return 1;
        }
        return -1;
    }

    /**
     * Make parent role valid.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (condition != null) {
            condition.setExpressionContainer(this);
        }
        if (message != null) {
            message.setExpressionContainer(this);
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
        if (condition == p) {
            Expression r = (Expression) q;
            condition = r;
            if (r != null) {
                r.setExpressionContainer(this);
            }
            return true;
        }
        if (message == p) {
            Expression r = (Expression) q;
            message = r;
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
        int c = 0;
        if (condition != null) {
            c++;
        }
        if (message != null) {
            c++;
        }
        return c;
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression
     * array. @param index an index for an expression. @return the expression with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */
    public Expression getExpressionAt(int index) {
        if (condition != null) {
            if (index == 0) {
                return condition;
            }
            index -= 1;
        }
        if (message != null) {
            if (index == 0) {
                return message;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Gets the condition expression.
     *
     * @return the expression.
     */
    public Expression getCondition() {
        return condition;
    }

    /**
     * Sets the condition expression.
     *
     * @param expr an expression.
     */
    public void setCondition(Expression expr) {
        condition = expr;
    }

    /**
     * Gets the message expression.
     *
     * @return the expression.
     */
    public Expression getMessage() {
        return message;
    }

    /**
     * Sets the message expression.
     *
     * @param expr an expression.
     */
    public void setMessage(Expression expr) {
        message = expr;
    }

    public void accept(SourceVisitor v) {
        v.visitAssert(this);
    }
}
