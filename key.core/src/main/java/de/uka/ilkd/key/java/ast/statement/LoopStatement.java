/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.speclang.jml.JmlSpec;

import org.key_project.util.ExtList;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.parsing.Position;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

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

    protected final ImmutableList<JmlSpec> attachedJml;

    /**
     * The translated loop invariant, attached directly to this loop node. Used to live in the
     * {@code SpecificationRepository}'s {@code (loop, line)} map; it is now node-attached so that
     * the repository can be deleted (see the JMLtk front-end rewrite project).
     */
    private @Nullable LoopSpecification loopInvariant;

    /**
     * The loop contracts applying directly to this loop (as opposed to the {@code StatementBlock}
     * containing it), attached to the node; former {@code loopContractsOnLoops} map.
     */
    private ImmutableSet<LoopContract> loopContracts = DefaultImmutableSet.nil();

    /**
     * Loop statement.
     *
     * @param body
     *        a statement.
     */
    public LoopStatement(@NonNull Expression guard, @NonNull Statement body, ExtList comments) {
        super(comments);
        this.body = body;
        this.updates = null;
        this.inits = null;
        this.guard = new Guard(guard);
        this.attachedJml = ImmutableList.nil();
    }

    public LoopStatement(Expression guard, @NonNull Statement body, ExtList comments,
            PositionInfo pos) {
        super(add(comments, pos));
        this.body = body;
        this.updates = null;
        this.inits = null;
        this.guard = new Guard(guard);
        this.attachedJml = ImmutableList.nil();
    }

    public LoopStatement(Expression guard, @NonNull Statement body) {
        this.body = body;
        this.updates = null;
        this.inits = null;
        this.guard = new Guard(guard);
        this.attachedJml = ImmutableList.nil();
    }

    public LoopStatement(Expression guard, @NonNull Statement body, PositionInfo pos) {
        super(pos);
        this.body = body;
        this.updates = null;
        this.inits = null;
        this.guard = new Guard(guard);
        this.attachedJml = ImmutableList.nil();
    }


    /**
     * Loop statement. This constructor is used for the transformation of Recoder to KeY.
     *
     * @param inits
     *        the initializers of the loop
     * @param guard
     *        the guard of the loop
     * @param updates
     *        the updates of the loop
     * @param body
     *        the body of the loop
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
        this.attachedJml = ImmutableList.nil();
    }

    /**
     * Loop statement. This constructor is used for the transformation of Recoder to KeY.
     *
     * @param inits
     *        the initializers of the loop
     * @param guard
     *        the guard of the loop
     * @param updates
     *        the updates of the loop
     * @param body
     *        the body of the loop
     * @param comments
     *        the comments attached to this statement.
     */
    public LoopStatement(ILoopInit inits, @NonNull IGuard guard, IForUpdates updates,
            @NonNull Statement body,
            ExtList comments) {
        super(comments);
        this.body = body;
        this.updates = updates;
        this.inits = inits;
        this.guard = guard;
        this.attachedJml = ImmutableList.nil();
    }


    public LoopStatement(ILoopInit inits, @NonNull IGuard guard, IForUpdates updates,
            @NonNull Statement body,
            ExtList comments, PositionInfo pos) {
        super(add(comments, pos));
        this.body = body;
        this.updates = updates;
        this.inits = inits;
        this.guard = guard;
        this.attachedJml = ImmutableList.nil();
    }


    /**
     * Loop statement. This constructor is used for the transformation of Recoder to KeY.
     *
     * @param inits
     *        the initializers of the loop
     * @param guard
     *        the guard of the loop
     * @param updates
     *        the updates of the loop
     * @param body
     *        the body of the loop
     * @param pos
     *        the position of the loop
     */
    public LoopStatement(ILoopInit inits, @NonNull IGuard guard, IForUpdates updates,
            @NonNull Statement body,
            PositionInfo pos) {
        super(pos);
        this.body = body;
        this.updates = updates;
        this.inits = inits;
        this.guard = guard;
        this.attachedJml = ImmutableList.nil();
    }


    /**
     * Loop statement. This constructor is used for the transformation of Recoder to KeY.
     *
     * @param inits
     *        the initializers of the loop
     * @param guard
     *        the guard of the loop
     * @param updates
     *        the updates of the loop
     * @param body
     *        the body of the loop
     */
    public LoopStatement(ILoopInit inits, @NonNull IGuard guard, IForUpdates updates,
            @NonNull Statement body) {
        this.body = body;
        this.updates = updates;
        this.inits = inits;
        this.guard = guard;
        this.attachedJml = ImmutableList.nil();
    }

    public LoopStatement(PositionInfo pi, List<Comment> comments, ILoopInit inits,
            IForUpdates updates, @NonNull IGuard guard, @NonNull Statement body,
            ImmutableList<JmlSpec> attachedJml) {
        super(pi, comments);
        this.inits = inits;
        this.updates = updates;
        this.guard = guard;
        this.body = body;
        this.attachedJml = attachedJml;
    }

    static private ExtList add(ExtList e, Object o) {
        e.add(o);
        return e;
    }

    @Override
    public ImmutableList<JmlSpec> getAttachedJml() {
        return attachedJml;
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
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException
     *            if <tt>index</tt> is out of bounds
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

    // ----------------------------------------------------------------------
    // node-attached (translated) specifications — formerly SpecificationRepository state
    // ----------------------------------------------------------------------

    /**
     * Returns the loop invariant attached to this loop, or {@code null} if none.
     */
    public @Nullable LoopSpecification getLoopInvariant() {
        return loopInvariant;
    }

    /**
     * Attaches the given loop invariant to this loop, replacing any previous one.
     */
    public void setLoopInvariant(@Nullable LoopSpecification inv) {
        this.loopInvariant = inv;
    }

    /**
     * Copies the invariant attached to this loop onto <code>to</code>, re-binding it to
     * <code>to</code>. Does nothing if this loop carries no invariant.
     *
     * @param to the loop that receives the invariant.
     * @see LoopSpecification#setLoop(LoopStatement)
     */
    public void copyLoopInvariantTo(LoopStatement to) {
        LoopSpecification inv = getLoopInvariant();
        if (inv != null) {
            to.setLoopInvariant(inv.setLoop(to));
        }
    }

    /**
     * Returns the loop contracts applying to this loop itself.
     */
    public ImmutableSet<LoopContract> getLoopContracts() {
        return loopContracts;
    }

    /**
     * Replaces the set of loop contracts attaching to this loop.
     */
    public void setLoopContracts(ImmutableSet<LoopContract> contracts) {
        this.loopContracts = contracts == null ? DefaultImmutableSet.nil() : contracts;
    }

    /**
     * Registers the given loop contract on this loop.
     */
    public void addLoopContract(LoopContract contract) {
        this.loopContracts = this.loopContracts.add(contract);
    }

    /**
     * Removes the given loop contract from this loop.
     */
    public void removeLoopContract(LoopContract contract) {
        this.loopContracts = this.loopContracts.remove(contract);
    }

}
