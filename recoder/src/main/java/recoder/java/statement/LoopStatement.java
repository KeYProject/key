/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.*;
import recoder.java.expression.ExpressionStatement;
import recoder.list.generic.ASTList;

/**
 * Loop statement.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class LoopStatement extends JavaStatement
        implements StatementContainer, ExpressionContainer {

    /**
     * Guard.
     */

    protected Expression guard;

    /**
     * Inits.
     */

    protected ASTList<LoopInitializer> inits;

    /**
     * Updates.
     */

    protected ASTList<Expression> updates;

    /**
     * Body.
     */

    protected Statement body;

    /**
     * Loop statement.
     */

    public LoopStatement() {
        // nothing to do
    }

    /**
     * Loop statement.
     *
     * @param body a statement.
     */

    public LoopStatement(Statement body) {
        setBody(body);
    }

    /**
     * Loop statement.
     *
     * @param proto a loop statement.
     */

    protected LoopStatement(LoopStatement proto) {
        super(proto);
        if (proto.guard != null) {
            guard = proto.guard.deepClone();
        }
        if (proto.inits != null) {
            inits = proto.inits.deepClone();
        }
        if (proto.updates != null) {
            updates = proto.updates.deepClone();
        }
        if (proto.body != null) {
            body = proto.body.deepClone();
        }
        // makeParentRoleValid() called by subclasses' constructors
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (inits != null) {
            for (int i = inits.size() - 1; i >= 0; i -= 1) {
                LoopInitializer li = inits.get(i);
                if (li instanceof ExpressionStatement) {
                    ((ExpressionStatement) li).setExpressionContainer(this);
                } else {
                    // LocalVariableDeclaration
                    li.setStatementContainer(this);
                }
            }
        }
        if (guard != null) {
            guard.setExpressionContainer(this);
        }
        if (updates != null) {
            for (int i = updates.size() - 1; i >= 0; i -= 1) {
                updates.get(i).setExpressionContainer(this);
            }
        }
        if (body != null) {
            body.setStatementContainer(this);
        }
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (inits != null) {
            result += inits.size();
        }
        if (guard != null) {
            result++;
        }
        if (updates != null) {
            result += updates.size();
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
        int len;
        if (inits != null) {
            len = inits.size();
            if (len > index) {
                return inits.get(index);
            }
            index -= len;
        }
        if (isCheckedBeforeIteration()) {
            if (guard != null) {
                if (index == 0) {
                    return guard;
                }
                index--;
            }
        }
        if (updates != null) {
            len = updates.size();
            if (len > index) {
                return updates.get(index);
            }
            index -= len;
        }
        if (body != null) {
            if (index == 0) {
                return body;
            }
            index--;
        }
        if (!isCheckedBeforeIteration()) {
            if (guard != null) {
                if (index == 0) {
                    return guard;
                }
                index--;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 (IDX): init (For only)
        // role 1: guard
        // role 2 (IDX): update (For only)
        // role 3: body
        if (inits != null) {
            int index = inits.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 0;
            }
        }
        if (guard == child) {
            return 1;
        }
        if (updates != null) {
            int index = updates.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 2;
            }
        }
        if (body == child) {
            return 3;
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
     * @param p the new child.
     * @return true if a replacement has occured, false otherwise.
     * @throws ClassCastException if the new child cannot take over the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        int count;
        if (p == null) {
            throw new NullPointerException();
        }
        count = (inits == null) ? 0 : inits.size();
        for (int i = 0; i < count; i++) {
            if (inits.get(i) == p) {
                if (q == null) {
                    inits.remove(i);
                } else {
                    LoopInitializer r = (LoopInitializer) q;
                    inits.set(i, r);
                    if (r instanceof ExpressionStatement) {
                        ((ExpressionStatement) r).setExpressionContainer(this);
                    } else {
                        r.setStatementContainer(this);
                    }
                }
                return true;
            }
        }
        if (guard == p) {
            Expression r = (Expression) q;
            guard = r;
            if (r != null) {
                r.setExpressionContainer(this);
            }
            return true;
        }
        count = (updates == null) ? 0 : updates.size();
        for (int i = 0; i < count; i++) {
            if (updates.get(i) == p) {
                if (q == null) {
                    updates.remove(i);
                } else {
                    Expression r = (Expression) q;
                    updates.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        if (body == p) {
            Statement r = (Statement) q;
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
        int result = 0;
        if (guard != null) {
            result += 1;
        }
        if (inits != null) {
            for (int i = inits.size() - 1; i >= 0; i -= 1) {
                if (inits.get(i) instanceof Expression) {
                    result += 1;
                }
            }
        }
        if (updates != null) {
            result += updates.size();
        }
        return result;
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression
     * array. @param index an index for an expression. @return the expression with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Expression getExpressionAt(int index) {
        if (guard != null) {
            if (index == 0) {
                return guard;
            }
            index -= 1;
        }
        if (inits != null) {
            int s = inits.size();
            for (int i = 0; i < s && index >= 0; i++) {
                LoopInitializer ii = inits.get(i);
                if (ii instanceof Expression) {
                    if (index == 0) {
                        return (Expression) ii;
                    }
                    index -= 1;
                }
            }
        }
        if (updates != null) {
            return updates.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get guard.
     *
     * @return the expression.
     */

    public Expression getGuard() {
        return guard;
    }

    /**
     * Set guard.
     *
     * @param expr an expression.
     */

    public void setGuard(Expression expr) {
        guard = expr;
    }

    /**
     * Get body.
     *
     * @return the statement.
     */

    public Statement getBody() {
        return body;
    }

    /**
     * Set body.
     *
     * @param statement a statement.
     */

    public void setBody(Statement statement) {
        body = statement;
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

    /**
     * Get initializers.
     *
     * @return the loop initializer mutable list.
     */

    public ASTList<LoopInitializer> getInitializers() {
        return inits;
    }

    /**
     * Set initializers.
     *
     * @param list a loop initializer mutable list.
     */
    public void setInitializers(ASTList<LoopInitializer> list) {
        inits = list;
    }

    /**
     * Get updates.
     *
     * @return the expression mutable list.
     */

    public ASTList<Expression> getUpdates() {
        return updates;
    }

    /**
     * Set updates.
     *
     * @param list an expression mutable list.
     */
    public void setUpdates(ASTList<Expression> list) {
        updates = list;
    }

    /**
     * Is exit condition.
     *
     * @return the boolean value.
     */

    public abstract boolean isExitCondition();

    /**
     * Is checked before iteration.
     *
     * @return the boolean value.
     */

    public abstract boolean isCheckedBeforeIteration();
}
