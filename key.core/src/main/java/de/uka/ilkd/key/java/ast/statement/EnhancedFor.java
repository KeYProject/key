/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;

/**
 * The new enhanced form of a for-loop.
 * <p>
 * for(Type var : exp) Statement
 * <p>
 * LoopStatement.inits is initialized with "Type var" LoopStatement.guard is initialized with "exp"
 * LoopStatement.body with "statement"
 *
 * @author mulbrich
 */
public class EnhancedFor extends LoopStatement implements VariableScope {
    private EnhancedFor(PositionInfo pi, List<Comment> comments, ILoopInit inits,
            IForUpdates updates, IGuard guard, Statement body) {
        super(pi, comments, inits, updates, guard, body);
    }

    public EnhancedFor(PositionInfo pi, List<Comment> comments, ILoopInit inits,
            IGuard guard, Statement body) {
        super(pi, comments, inits, null, guard, body);
    }


    /**
     * Used for the Recoder2KeY transformation.
     *
     * @param init the initializers - here a single VariableDeclaration. may not be null.
     * @param guard a guard - here an expression of type Iterable. may not be null.
     * @param statement the statement of the loop
     * @param comments collected comments
     * @param info position
     */
    public EnhancedFor(@NonNull LoopInit init, @NonNull Guard guard, @NonNull Statement statement,
            ExtList comments, PositionInfo info) {
        this(info, null, init, null, guard, statement);
    }

    /**
     * Used by the {@link CreatingASTVisitor}.
     *
     * @param children a list of parameters
     */
    public EnhancedFor(ExtList children) {
        super(children.get(ILoopInit.class), children.get(IGuard.class), null,
            children.get(Statement.class), children);
    }

    /**
     * @see For#getLastElement()
     * @see JavaSourceElement#getLastElement()
     */
    @Override
    @NonNull
    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     * @see For#isCheckedBeforeIteration
     */
    @Override
    public boolean isCheckedBeforeIteration() {
        // TODO (?)
        return true;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnEnhancedFor(this);
    }

    /**
     * get the local variable declaration of the enhanced for-loop <code>for(type var : exp)</code>
     * gives <code>type var</code>.
     *
     * @return the local variable declaration.
     */
    public LocalVariableDeclaration getVariableDeclaration() {
        return (LocalVariableDeclaration) getInitializers().get(0);
    }
}
