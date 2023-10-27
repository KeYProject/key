/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.*;

/**
 * Synchronized block.
 *
 * @author <TT>AutoDoc</TT>
 */

public class SynchronizedBlock extends JavaStatement
        implements StatementContainer, ExpressionContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -9179480508765855081L;

    /**
     * Expression.
     */

    protected Expression expression;

    /**
     * Body.
     */

    protected StatementBlock body;

    /**
     * Synchronized block.
     */

    public SynchronizedBlock() {
        // nothing to do
    }

    /**
     * Synchronized block.
     *
     * @param body a statement block.
     */

    public SynchronizedBlock(StatementBlock body) {
        setBody(body);
        makeParentRoleValid();
    }

    /**
     * Synchronized block.
     *
     * @param e an expression.
     * @param body a statement block.
     */

    public SynchronizedBlock(Expression e, StatementBlock body) {
        setExpression(e);
        setBody(body);
        makeParentRoleValid();
    }

    /**
     * Synchronized block.
     *
     * @param proto a synchronized block.
     */

    protected SynchronizedBlock(SynchronizedBlock proto) {
        super(proto);
        if (proto.expression != null) {
            expression = proto.expression.deepClone();
        }
        if (proto.body != null) {
            body = proto.body.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public SynchronizedBlock deepClone() {
        return new SynchronizedBlock(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (body != null) {
            body.setStatementContainer(this);
        }
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
        if (body == p) {
            StatementBlock r = (StatementBlock) q;
            body = r;
            if (r != null) {
                r.setStatementContainer(this);
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
     * @param e an expression.
     */

    public void setExpression(Expression e) {
        expression = e;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (expression != null) {
            result++;
        }
        if (body != null) {
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
        if (expression != null) {
            if (index == 0) {
                return expression;
            }
            index--;
        }
        if (body != null) {
            if (index == 0) {
                return body;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: expression
        // role 1: body
        if (expression == child) {
            return 0;
        }
        if (body == child) {
            return 1;
        }
        return -1;
    }

    /**
     * Get body.
     *
     * @return the statement block.
     */

    public StatementBlock getBody() {
        return body;
    }

    /**
     * Set body.
     *
     * @param body a statement block.
     */

    public void setBody(StatementBlock body) {
        this.body = body;
    }

    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */

    public int getStatementCount() {
        return (body != null) ? 1 : 0;
    }

    /*
     * Return the statement at the specified index in this node's "virtual" statement array. @param
     * index an index for a statement. @return the statement with the given index. @exception
     * ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public void accept(SourceVisitor v) {
        v.visitSynchronizedBlock(this);
    }
}
