/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.*;

/**
 * If.
 *
 * @author <TT>AutoDoc</TT>
 */

public class If extends BranchStatement implements ExpressionContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -6352480723638689470L;

    /**
     * Then branch.
     */

    protected Then thenBranch;

    /**
     * Else branch.
     */

    protected Else elseBranch;

    /**
     * Expression.
     */

    protected Expression expression;

    /**
     * If.
     */

    public If() {
        // nothing to do
    }

    /**
     * If.
     *
     * @param e an expression.
     * @param thenStatement a statement.
     */

    public If(Expression e, Statement thenStatement) {
        this(e, thenStatement, null);
    }

    /**
     * If.
     *
     * @param e an expression.
     * @param thenBranch a then.
     */

    public If(Expression e, Then thenBranch) {
        this(e, thenBranch, null);
    }

    /**
     * If.
     *
     * @param e an expression.
     * @param thenBranch a then.
     * @param elseBranch an else.
     */

    public If(Expression e, Then thenBranch, Else elseBranch) {
        if (e == null) {
            throw new NullPointerException();
        }
        expression = e;
        setThen(thenBranch);
        setElse(elseBranch);
        makeParentRoleValid();
    }

    /**
     * If.
     *
     * @param e an expression.
     * @param thenStatement a statement.
     * @param elseStatement a statement.
     */

    public If(Expression e, Statement thenStatement, Statement elseStatement) {
        if (e == null) {
            throw new NullPointerException();
        }
        expression = e;
        setThen(getFactory().createThen(thenStatement));
        if (elseStatement != null) {
            setElse(getFactory().createElse(elseStatement));
        }
        makeParentRoleValid();
    }

    /**
     * If.
     *
     * @param proto an if.
     */

    protected If(If proto) {
        super(proto);
        if (proto.thenBranch != null) {
            thenBranch = proto.thenBranch.deepClone();
        }
        if (proto.elseBranch != null) {
            elseBranch = proto.elseBranch.deepClone();
        }
        if (proto.expression != null) {
            expression = proto.expression.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public If deepClone() {
        return new If(this);
    }

    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
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
        if (thenBranch != null) {
            result++;
        }
        if (elseBranch != null) {
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
        if (thenBranch != null) {
            if (index == 0) {
                return thenBranch;
            }
            index--;
        }
        if (elseBranch != null) {
            if (index == 0) {
                return elseBranch;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: expression
        // role 1: then
        // role 2: else
        if (expression == child) {
            return 0;
        }
        if (thenBranch == child) {
            return 1;
        }
        if (elseBranch == child) {
            return 2;
        }
        return -1;
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (expression != null) {
            expression.setExpressionContainer(this);
        }
        if (thenBranch != null) {
            thenBranch.setParent(this);
        }
        if (elseBranch != null) {
            elseBranch.setParent(this);
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
        if (thenBranch == p) {
            Then r = (Then) q;
            thenBranch = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        if (elseBranch == p) {
            Else r = (Else) q;
            elseBranch = r;
            if (r != null) {
                r.setParent(this);
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
     * Get then.
     *
     * @return the then.
     */

    public Then getThen() {
        return thenBranch;
    }

    /**
     * Set then.
     *
     * @param thenBranch a then.
     */

    public void setThen(Then thenBranch) {
        this.thenBranch = thenBranch;
    }

    /**
     * Get else.
     *
     * @return the else.
     */

    public Else getElse() {
        return elseBranch;
    }

    /**
     * Set else.
     *
     * @param elseBranch an else.
     */

    public void setElse(Else elseBranch) {
        this.elseBranch = elseBranch;
    }

    /**
     * Get the number of branches in this container.
     *
     * @return the number of branches.
     */

    public int getBranchCount() {
        int result = 0;
        if (thenBranch != null) {
            result += 1;
        }
        if (elseBranch != null) {
            result += 1;
        }
        return result;
    }

    /*
     * Return the branch at the specified index in this node's "virtual" branch array. @param index
     * an index for a branch. @return the branch with the given index. @exception
     * ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Branch getBranchAt(int index) {
        if (thenBranch != null) {
            if (index == 0) {
                return thenBranch;
            }
            index -= 1;
        }
        if (elseBranch != null) {
            if (index == 0) {
                return elseBranch;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public void accept(SourceVisitor v) {
        v.visitIf(this);
    }
}
