/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.*;
import recoder.list.generic.ASTList;

/**
 * Case.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Case extends Branch implements ExpressionContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 4344680443480425524L;

    /**
     * Expression.
     */

    protected Expression expression;

    /**
     * Body.
     */

    protected ASTList<Statement> body;

    /**
     * Case.
     */

    public Case() {
        super();
    }

    /**
     * Case.
     *
     * @param e an expression.
     */

    public Case(Expression e) {
        setExpression(e);
        makeParentRoleValid();
    }

    /**
     * Case.
     *
     * @param e an expression.
     * @param body a statement mutable list.
     */

    public Case(Expression e, ASTList<Statement> body) {
        setBody(body);
        setExpression(e);
        makeParentRoleValid();
    }

    /**
     * Case.
     *
     * @param proto a case.
     */

    protected Case(Case proto) {
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

    public Case deepClone() {
        return new Case(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (expression != null) {
            expression.setExpressionContainer(this);
        }
        if (body != null) {
            for (Statement statement : body) {
                statement.setStatementContainer(this);
            }
        }
    }

    @Override
    public Switch getParent() {
        return (Switch) parent;
    }

    /**
     * Set parent.
     *
     * @param parent a switch.
     */

    public void setParent(Switch parent) {
        this.parent = parent;
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
            result += body.size();
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
        int len;
        if (expression != null) {
            if (index == 0) {
                return expression;
            }
            index--;
        }
        if (body != null) {
            len = body.size();
            if (len > index) {
                return body.get(index);
            }
            index -= len;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: expression
        // role 1 (IDX): body
        if (expression == child) {
            return 0;
        }
        if (body != null) {
            int index = body.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 1;
            }
        }
        return -1;
    }

    /**
     * Replace a single child in the current node. The child to replace is matched by identity and
     * hence must be known exactly. The replacement element can be null - in that case, the child is
     * effectively removed. The parent role of the new child is validated, while the parent link of
     * the replaced child is left untouched.
     *
     * @param p the old child.
     * @param q the new child.
     * @return true if a replacement has occured, false otherwise.
     * @throws ClassCastException if the new child cannot take over the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        int count;
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
        count = (body == null) ? 0 : body.size();
        for (int i = 0; i < count; i++) {
            if (body.get(i) == p) {
                if (q == null) {
                    body.remove(i);
                } else {
                    Statement r = (Statement) q;
                    body.set(i, r);
                    r.setStatementContainer(this);
                }
                return true;
            }
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
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */

    public int getStatementCount() {
        return (body != null) ? body.size() : 0;
    }

    /*
     * Return the statement at the specified index in this node's "virtual" statement array. @param
     * index an index for a statement. @return the statement with the given index. @exception
     * ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Statement getStatementAt(int index) {
        if (body != null) {
            return body.get(index);
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
        if (e == null) {
            throw new NullPointerException("Cases must have an expression");
        }
        expression = e;
    }

    /**
     * The body may be empty (null), to define a fall-through. Attaching an
     * {@link EmptyStatement}would create a single ";".
     */

    public ASTList<Statement> getBody() {
        return body;
    }

    /**
     * Set body.
     *
     * @param list a statement mutable list.
     */

    public void setBody(ASTList<Statement> list) {
        body = list;
    }

    public void accept(SourceVisitor v) {
        v.visitCase(this);
    }

    public SourceElement getLastElement() {
        if (body == null || body.size() == 0) {
            return this;
        }
        return body.get(body.size() - 1).getLastElement();
    }
}
