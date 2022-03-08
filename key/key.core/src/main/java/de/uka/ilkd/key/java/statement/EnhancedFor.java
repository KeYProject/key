// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import java.util.List;

/**
 * The new enhanced form of a for-loop.
 * <p>
 * for(Type var : exp) Statement
 * <p>
 * LoopStatement.inits is initialized with "Type var" LoopStatement.guard is
 * initialized with "exp" LoopStatement.body with "statement"
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
     * @param init      the initializers - here a single VariableDeclaration. may not be null.
     * @param guard     a guard - here an expression of type Iterable. may not be null.
     * @param statement the statement of the loop
     * @param comments  collected comments
     * @param info      position
     */
    public EnhancedFor(@Nonnull LoopInit init, @Nonnull Guard guard, @Nonnull Statement statement,
                       ExtList comments, PositionInfo info) {
        this(info, null, init, null, guard, statement);
    }

    /**
     * Used by the {@link CreatingASTVisitor}.
     *
     * @param children a list of parameters
     */
    public EnhancedFor(ExtList children) {
        super(children.get(ILoopInit.class), children
                .get(IGuard.class), null, children
                .get(Statement.class), children);
    }

    /**
     * @see de.uka.ilkd.key.java.statement.For#getLastElement()
     * @see de.uka.ilkd.key.java.JavaSourceElement#getLastElement()
     */
    @Override
    @Nonnull
    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     * @see de.uka.ilkd.key.java.statement.For#isCheckedBeforeIteration
     * @see recoder.java.statement.LoopStatement#isCheckedBeforeIteration()
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

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printEnhancedFor(this);
    }

    /**
     * get the local variable declaration of the enhanced for-loop
     * <code>for(type var : exp)</code> gives <code>type var</code>.
     *
     * @return the local variable declaration.
     */
    public LocalVariableDeclaration getVariableDeclaration() {
        return (LocalVariableDeclaration) getInitializers().get(0);
    }

}