/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.expression.Expression;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Loop statement.
 *
 */

public abstract class LoopStatement extends JavaStatement
        implements StatementContainer, ExpressionContainer {


    /**
     * Inits.
     */
    protected final ILoopInit inits;

    /**
     * Updates.
     */
    protected final IForUpdates updates;


    /**
     * Guard.
     */
    @NonNull
    protected final IGuard guard;


    /**
     * Body.
     */
    @NonNull
    protected final Statement body;

    /**
     * Loop statement.
     *
     * @param body a statement.
     */
    public LoopStatement(@NonNull Expression guard, @NonNull Statement body, ExtList comments) {
        super(comments);
        this.body = body;
        this.updates = null;
        this.inits = null;
        this.guard = new Guard(guard);
    }


    public LoopStatement(Expression guard, @NonNull Statement body, ExtList comments,
            PositionInfo pos) {
        super(add(comments, pos));
        this.body = body;
        this.updates = null;
        this.inits = null;
        this.guard = new Guard(guard);
    }


    /**
     * Loop statement.
     *
     * @param body a statement.
     */
    public LoopStatement(Expression guard, @NonNull Statement body) {
        this.body = body;
        this.updates = null;
        this.inits = null;
        this.guard = new Guard(guard);
    }

    public LoopStatement(Expression guard, @NonNull Statement body, PositionInfo pos) {
        super(pos);
        this.body = body;
        this.updates = null;
        this.inits = null;
        this.guard = new Guard(guard);
    }


    /**
     * Loop statement. This constructor is used for the transformation of Recoder to KeY.
     *
     * @param inits the initializers of the loop
     * @param guard the guard of the loop
     * @param updates the updates of the loop
     * @param body the body of the loop
     */
    public LoopStatement(LoopInitializer[] inits, Expression guard, Expression[] updates,
            @NonNull Statement body) {
        this.body = body;
        if (updates != null) {
            this.updates = new ForUpdates(new ImmutableArray<>(updates));
        } else {
            this.updates = new ForUpdates(new ImmutableArray<>(new Expression[0]));
        }
        this.inits = new LoopInit(inits);
        this.guard = new Guard(guard);
    }

    /**
     * Loop statement. This constructor is used for the transformation of Recoder to KeY.
     *
     * @param inits the initializers of the loop
     * @param guard the guard of the loop
     * @param updates the updates of the loop
     * @param body the body of the loop
     * @param comments the comments attached to this statement.
     */
    public LoopStatement(ILoopInit inits, @NonNull IGuard guard, IForUpdates updates,
            @NonNull Statement body,
            ExtList comments) {
        super(comments);
        this.body = body;
        this.updates = updates;
        this.inits = inits;
        this.guard = guard;
    }


    public LoopStatement(ILoopInit inits, @NonNull IGuard guard, IForUpdates updates,
            @NonNull Statement body,
            ExtList comments, PositionInfo pos) {
        super(add(comments, pos));
        this.body = body;
        this.updates = updates;
        this.inits = inits;
        this.guard = guard;
    }


    /**
     * Loop statement. This constructor is used for the transformation of Recoder to KeY.
     *
     * @param inits the initializers of the loop
     * @param guard the guard of the loop
     * @param updates the updates of the loop
     * @param body the body of the loop
     * @param pos the position of the loop
     */
    public LoopStatement(ILoopInit inits, @NonNull IGuard guard, IForUpdates updates,
            @NonNull Statement body,
            PositionInfo pos) {
        super(pos);
        this.body = body;
        this.updates = updates;
        this.inits = inits;
        this.guard = guard;
    }


    /**
     * Loop statement. This constructor is used for the transformation of Recoder to KeY.
     *
     * @param inits the initializers of the loop
     * @param guard the guard of the loop
     * @param updates the updates of the loop
     * @param body the body of the loop
     */
    public LoopStatement(ILoopInit inits, @NonNull IGuard guard, IForUpdates updates,
            @NonNull Statement body) {
        this.body = body;
        this.updates = updates;
        this.inits = inits;
        this.guard = guard;
    }

    public LoopStatement(PositionInfo pi, List<Comment> comments, ILoopInit inits,
            IForUpdates updates, @NonNull IGuard guard, @NonNull Statement body) {
        super(pi, comments);
        this.inits = inits;
        this.updates = updates;
        this.guard = guard;
        this.body = body;

    }

    static private ExtList add(ExtList e, Object o) {
        e.add(o);
        return e;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (inits != null) {
            result++;
        }
        if (guard != null) {
            result++;
        }
        if (updates != null) {
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
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (inits != null) {
            if (index == 0) {
                return inits;
            }
            index--;
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
            if (index == 0) {
                return updates;
            }
            index--;
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
            result += 1;
        }
        if (updates != null) {
            result += updates.size();
        }
        return result;
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression array.
     *
     * @param index an index for an expression.
     *
     * @return the expression with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    public Expression getExpressionAt(int index) {
        if (guard != null) {
            if (index == 0) {
                return (Expression) guard.getChildAt(0);
            }
            index -= 1;
        }
        if (inits != null) {
            int s = inits.size();
            for (int i = 0; i < s && index >= 0; i++) {
                final LoopInitializer ii = inits.getInits().get(i);
                if (ii instanceof Expression) {
                    if (index == 0) {
                        return (Expression) ii;
                    }
                    index -= 1;
                }
            }
        }
        if (updates != null) {
            return updates.getExpressionAt(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get guard.
     *
     * @return the expression.
     */
    @NonNull
    public IGuard getGuard() {
        return guard;
    }

    /**
     * Get guard.
     *
     * @return the expression.
     */
    @Nullable
    public Expression getGuardExpression() {
        return (Expression) guard.getChildAt(0);
    }

    /**
     * Get body.
     *
     * @return the statement.
     */
    @NonNull
    public Statement getBody() {
        return body;
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
     * Return the statement at the specified index in this node's "virtual" statement array.
     *
     * @param index an index for a statement.
     *
     * @return the statement with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
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
     * @return the loop initializer array wrapper .
     */
    public ImmutableArray<LoopInitializer> getInitializers() {
        if (inits != null) {
            return inits.getInits();
        }
        return null;
    }


    /**
     * Get updates.
     *
     * @return the expression mutable list.
     */
    public ImmutableArray<Expression> getUpdates() {
        if (updates != null) {
            return updates.getUpdates();
        }
        return null;
    }

    /**
     * Get updates as IForUpdates
     *
     * @return the expression mutable list.
     */
    public IForUpdates getIForUpdates() {
        return updates;
    }

    /**
     * get the loop initializer as ILoopInit
     *
     * @return the loop initializer
     */
    public ILoopInit getILoopInit() {
        return inits;
    }

    /**
     * Is checked before iteration.
     *
     * @return the boolean value.
     */
    public abstract boolean isCheckedBeforeIteration();

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof LoopStatement cmp)) {
            return false;
        }

        return super.equals(cmp) && (this.getStartPosition().equals(Position.UNDEFINED)
                || cmp.getStartPosition().equals(Position.UNDEFINED)
                || this.getStartPosition().line() == cmp.getStartPosition().line());
    }

}
